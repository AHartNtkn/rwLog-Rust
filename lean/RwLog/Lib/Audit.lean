/-
# Checks of a whole library, made by the build

Two commands, for the files that say what a library rests on
(`AxiomAudit.lean`) and what a rung claims (`Manifest/`). Neither takes a
list of names kept by hand for the whole library, so a theorem a thread adds
is checked without anyone remembering to list it.

* `#audit_library L₁ L₂ …`, for libraries whose root directories stand beside
  the file that has the command. For each library `L` it fails unless

  * every file under the directory `L/` is a module the file imports (so no
    file is out of the build), and
  * no declaration of a module of `L` depends on an axiom other than the
    three standard ones, `propext`, `Classical.choice` and `Quot.sound`. A
    proof with `sorry` depends on `sorryAx` and fails here.

  When it fails it names the files, or the axioms and the first declarations
  that use them.

* `#assert_axioms n₁ n₂ …` fails unless each of the named declarations
  depends on the three standard axioms only. A manifest uses it to name the
  headline theorems of a rung.

* `#trusted_files p` lists, as a message, the modules with the prefix `p`
  among everything the file imports, and the other modules of the library
  whose definitions they are written with (what they import, directly or
  through other modules). A manifest puts it under `#guard_msgs`, so the
  build fails when what a rung trusts changes.

* `#shared_layers p₁ p₂ …` fails unless the modules with these prefixes import
  only each other, among the modules of their library. It is how the build
  holds the shared layers to never importing a machine.
-/
import Lean

open Lean Elab Command

namespace RwLog.Audit

/-- The axioms a proof may rest on. -/
def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms reachable from a constant, added to those found so far. The
constants visited are remembered, so a pass over many constants visits each
constant of the environment once. -/
partial def reach (env : Environment) (c : Name) : StateM (NameSet × NameSet) Unit := do
  if (← get).1.contains c then return
  modify fun s => (s.1.insert c, s.2)
  let expr (e : Expr) : StateM (NameSet × NameSet) Unit := e.getUsedConstants.forM (reach env)
  match env.checked.get.find? c with
  | some (.axiomInfo v) =>
    modify fun s => (s.1, s.2.insert c)
    expr v.type
  | some (.defnInfo v) => expr v.type *> expr v.value
  | some (.thmInfo v) => expr v.type *> expr v.value
  | some (.opaqueInfo v) => expr v.type *> expr v.value
  | some (.quotInfo _) => pure ()
  | some (.ctorInfo v) => expr v.type
  | some (.recInfo v) => expr v.type
  | some (.inductInfo v) => expr v.type *> v.ctors.forM (reach env)
  | none => pure ()

/-- The axioms the constants of `cs` depend on, other than the standard
ones. -/
def nonStandard (env : Environment) (cs : Array Name) : Array Name :=
  let (_, s) := (cs.forM (reach env)).run ({}, {})
  (s.2.toArray.filter fun a => !standard.contains a).qsort Name.lt

/-- The module of the library `lib`: `lib` itself or a module below it. -/
def inLibrary (lib m : Name) : Bool := lib.isPrefixOf m

/-- The declarations of the modules of the library `lib`. -/
def declsOf (env : Environment) (lib : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc c _ =>
    match env.getModuleIdxFor? c with
    | some i => if inLibrary lib env.header.moduleNames[i.toNat]! then acc.push c else acc
    | none => acc

/-- The module a file stands for, from its path below the directory `root`. -/
def moduleOf (root file : System.FilePath) : Name :=
  let rel := (file.withExtension "").components.drop root.components.length
  rel.foldl (fun n s => Name.str n s) Name.anonymous

/-- The `.lean` files under the directory of the library `lib` beside the
file with the command that are not modules that file imports. -/
def filesOut (env : Environment) (root : System.FilePath) (lib : Name) : IO (Array Name) := do
  let dir := root / lib.toString
  unless ← dir.isDir do
    throw <| IO.userError s!"there is no directory {dir}"
  let files := (← dir.walkDir).filter fun f => f.extension == some "lean"
  let imported : NameSet := env.header.moduleNames.foldl (fun s m => s.insert m) {}
  return (files.map (moduleOf root)).filter (fun m => !imported.contains m) |>.qsort Name.lt

/-- `#audit_library L₁ L₂ …`: every file of each library is in the build, and
no declaration of it depends on an axiom other than the three standard
ones. -/
elab "#audit_library " libs:ident+ : command => do
  let env ← getEnv
  let root := (System.FilePath.mk (← getFileName)).parent.getD "."
  for l in libs do
    let lib := l.getId
    let out ← filesOut env root lib
    unless out.isEmpty do
      throwErrorAt l "files of {lib} that are not in the build: {out.toList}"
    let decls := declsOf env lib
    if decls.isEmpty then
      throwErrorAt l "no declaration of {lib} is imported"
    let bad := nonStandard env decls
    unless bad.isEmpty do
      let users := decls.filter (fun c => !(nonStandard env #[c]).isEmpty) |>.qsort Name.lt
      throwErrorAt l "declarations of {lib} depend on the axioms {bad.toList}; the first of them: {(users.extract 0 20).toList}"
    logInfoAt l m!"{lib}: {decls.size} declarations, each on the three standard axioms only, and every file in the build"

/-- `#assert_axioms n₁ n₂ …`: each named declaration depends on the three
standard axioms only. -/
elab "#assert_axioms " names:ident+ : command => do
  let env ← getEnv
  for n in names do
    let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
    let bad := nonStandard env #[c]
    unless bad.isEmpty do
      throwErrorAt n "{c} depends on the axioms {bad.toList}"

/-- The imports of each module, by name. -/
def importsOf (env : Environment) : NameMap (Array Name) :=
  (env.header.moduleNames.zip env.header.moduleData).foldl
    (fun m (n, d) => m.insert n (d.imports.map (·.module))) {}

/-- The first component of a name: the library of a module. -/
def rootOf : Name → Name
  | .str .anonymous s => .str .anonymous s
  | .str p _ => rootOf p
  | .num p _ => rootOf p
  | .anonymous => .anonymous

/-- The modules of the library of `p` that the modules with the prefix `p`
import, directly or through other modules, themselves included. -/
partial def closure (env : Environment) (p : Name) : Array Name :=
  let imps := importsOf env
  let lib := rootOf p
  let rec go (todo : List Name) (seen : NameSet) : NameSet :=
    match todo with
    | [] => seen
    | m :: rest =>
      if seen.contains m then go rest seen
      else
        let next := ((imps.find? m).getD #[]).toList.filter fun i => lib.isPrefixOf i
        go (next ++ rest) (seen.insert m)
  (go (env.header.moduleNames.filter fun m => p.isPrefixOf m).toList {}).toArray.qsort Name.lt

/-- `#trusted_files p`: as a message, the modules with the prefix `p` among
everything this file imports, and then the other modules of the library that
those import, directly or through other modules. A statement in a module with
the prefix `p` is written with the definitions of all of them, so all of them
are what a reader trusts. -/
elab "#trusted_files " p:ident : command => do
  let env ← getEnv
  let all := closure env p.getId
  let (own, others) := all.partition fun m => p.getId.isPrefixOf m
  logInfo m!"{own.map toString}\nand the definitions they are written with:\n{others.map toString}"

/-- `#shared_layers p₁ p₂ …`: the modules with these prefixes import no module
of their library that has none of these prefixes. So what is shared by every
rung is closed: nothing in it rests on one machine. -/
elab "#shared_layers " ps:ident+ : command => do
  let env ← getEnv
  let prefixes := ps.map (·.getId)
  let shared (m : Name) : Bool := prefixes.any fun p => p.isPrefixOf m
  let imps := importsOf env
  let mut bad : Array (Name × Name) := #[]
  for m in env.header.moduleNames do
    if shared m then
      for i in (imps.find? m).getD #[] do
        if (rootOf m).isPrefixOf i && !shared i then bad := bad.push (m, i)
  unless bad.isEmpty do
    throwError "shared modules that import a module that is not shared: {bad.toList}"

end RwLog.Audit
