/-
# The whole unfolding, read off its text

What `Unfold.eager` and the operations it is made of return at the derivation
kernel of a domain: each is the list its text builds (`glueV`, `seqProdV`,
`liftV`, `seqAllV`, `meetAllV`), and `eager` by the kind of node it reads
(`eager_span`, `eager_call`, `eager_union`, `eager_chain`, `eager_meet`).
-/
import RwLog.Rungs.Tabled.Unfolding.Sem
import RwLog.Rungs.Tabled.Unfold

namespace RwLog

namespace Tabled

namespace Unfold

open Answer Traverse

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- The products of an unfolding at the derivation kernel of a domain. -/
abbrev Pr (D : Domain R) (P : Program) := Unfold.Prod R (Ans D P)

omit [DecidableEq R] in
theorem mem_closedOf {ps : List (Pr D P)} {a : Ans D P} : a ∈ closedOf ps ↔ .closed a ∈ ps := by
  unfold closedOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, h⟩
    cases p with
    | closed b => cases h; exact hp
    | opn l r => cases h
  · exact fun h => ⟨_, h, rfl⟩

/-- Two stretches that meet, composed. -/
def glueV (D : Domain R) : Option R → Option R → Option (Option R)
  | none, y => some y
  | some x, none => some (some x)
  | some x, some y => (D.compose x y).map some

variable (K : Kernel R Cost) (hK : K.Refines D)

theorem glue_val (x y : Option R) :
    (glue (K := DerivationKernel.over D K hK P) x y).val = glueV D x y := by
  at_cost K hK
  cases x <;> cases y <;> simp [glue, glueV, hK.compose]

/-- A product followed by a product of the next member of a chain. -/
def seqProdV : Pr D P → Pr D P → Option (Pr D P)
  | .closed a, .closed b => (Ans.join D P K hK a b).val.map .closed
  | .closed a, .opn l r => (glueV D (some a.span) l).map fun l' => .opn l' r
  | .opn l r, .closed b => (glueV D r (some b.span)).map fun r' => .opn l r'
  | .opn l r, .opn l' r' => (glueV D r l').map fun _ => .opn l r'

theorem seqProd_val (p q : Pr D P) :
    (seqProd (K := DerivationKernel.over D K hK P) p q).val = seqProdV K hK p q := by
  have eg := glue_val (P := P) K hK
  cases p <;> cases q <;> simp only [seqProdV, ← eg] <;> (clear eg; at_cost K hK) <;>
    simp only [seqProd, Cost.bind_val, Cost.pure_val, over_join, over_span]

/-- Apply a rule to the answers among the products. -/
def liftV (f : Ans D P → Option (Ans D P)) (ps : List (Pr D P)) : List (Pr D P) :=
  ps.filterMap fun p => match p with
    | .closed a => (f a).map .closed
    | .opn l r => some (.opn l r)

theorem liftL_val (f : Ans D P → Cost (Option (Ans D P))) (ps : List (Pr D P)) :
    (liftL (K := DerivationKernel.over D K hK P) f ps).val = liftV (fun a => (f a).val) ps := by
  at_cost K hK
  simp only [liftL, liftV, filterMapL_std, Cost.filterMapL_val]
  congr 1
  funext p
  cases p <;> simp only [Cost.bind_val, Cost.pure_val]

/-- The products of a chain from the products of its members. -/
def seqAllV : List (List (Pr D P)) → List (Pr D P)
  | [] => []
  | ps :: rest => rest.foldl (fun acc qs => acc.flatMap fun p => qs.filterMap (seqProdV K hK p)) ps

theorem seqAll_val (pss : List (List (Pr D P))) :
    (seqAll (K := DerivationKernel.over D K hK P) pss).val = seqAllV K hK pss := by
  have es := seqProd_val (P := P) K hK
  at_cost K hK
  cases pss with
  | nil => rfl
  | cons ps rest =>
    simp only [seqAll, seqAllV, foldL_std, Cost.foldL_val, flatMapL_std, Cost.flatMapL_val,
      filterMapL_std, Cost.filterMapL_val, es]

/-- The closed products of a meet from the answers of its members. -/
def meetAllV : List (List (Ans D P)) → List (Ans D P)
  | [] => []
  | as :: rest => rest.foldl
      (fun acc bs => acc.flatMap fun a => bs.filterMap fun b => (Ans.meetA D P K hK a b).val) as

theorem meetAll_val (ass : List (List (Ans D P))) :
    (meetAll (K := DerivationKernel.over D K hK P) ass).val = meetAllV K hK ass := by
  at_cost K hK
  cases ass with
  | nil => rfl
  | cons as rest =>
    simp only [meetAll, meetAllV, foldL_std, Cost.foldL_val, flatMapL_std, Cost.flatMapL_val,
      filterMapL_std, Cost.filterMapL_val, over_meetA]

/-! ## The unfolding, by the kind of node -/

section eager

variable (d : Nat) (lb : Option R) (n : Rel) (rb : Option R)

theorem eager_zero :
    (eager (K := DerivationKernel.over D K hK P) 0 lb n rb).val = [.opn lb rb] := by
  at_cost K hK
  simp only [eager, Cost.pure_val]

theorem eager_span (h : n.view.forget = .span ()) :
    (eager (K := DerivationKernel.over D K hK P) (d + 1) lb n rb).val =
      (Ans.leaf D P K hK lb n rb).val.toList.map .closed := by
  at_cost K hK
  simp only [eager, Cost.bind_val, over_view, Charged.viewNode, Charged.op, h, Cost.pure_val,
    over_leaf]

theorem eager_call {m : Name} {f : Bool} {b : Rel} (h : n.view.forget = .call m f)
    (hb : Charged.bodyOf P n = some b) :
    (eager (K := DerivationKernel.over D K hK P) (d + 1) lb n rb).val =
      liftV (fun a => (Ans.unfold D P a n).val)
        (eager (K := DerivationKernel.over D K hK P) d lb b rb).val := by
  have el := liftL_val (P := P) K hK
  rw [← el]
  clear el
  at_cost K hK
  simp only [eager, Cost.bind_val, over_view, Charged.viewNode, Charged.op, h,
    over_body, Charged.body, hb]

theorem eager_union {xs : List Rel} (h : n.view.forget = .union xs) :
    (eager (K := DerivationKernel.over D K hK P) (d + 1) lb n rb).val =
      xs.zipIdx.flatMap fun p => liftV (fun a => (Ans.inj D P a n p.2).val)
        (eager (K := DerivationKernel.over D K hK P) d lb p.1 rb).val := by
  have el := liftL_val (P := P) K hK
  simp only [← el]
  clear el
  at_cost K hK
  simp only [eager, Cost.bind_val, over_view, Charged.viewNode, Charged.op, h,
    flatMapL_std, Cost.flatMapL_val]

theorem eager_chain {xs : List Rel} (h : n.view.forget = .chain xs) :
    (eager (K := DerivationKernel.over D K hK P) (d + 1) lb n rb).val =
      seqAllV K hK (xs.zipIdx.map fun p =>
        (eager (K := DerivationKernel.over D K hK P) d (if p.2 = 0 then lb else none) p.1
          (if p.2 + 1 = xs.length then rb else none)).val) := by
  have es := seqAll_val (P := P) K hK
  rw [← es]
  clear es
  at_cost K hK
  simp only [eager, Cost.bind_val, over_view, Charged.viewNode, Charged.op, h,
    mapL_std, Cost.mapL_val]

theorem eager_meet {xs : List Rel} (h : n.view.forget = .meet xs) :
    (eager (K := DerivationKernel.over D K hK P) (d + 1) lb n rb).val =
      (meetAllV K hK ((xs.map fun x =>
          (eager (K := DerivationKernel.over D K hK P) d lb x rb).val).map closedOf)).map .closed ++
        if ((xs.map fun x => (eager (K := DerivationKernel.over D K hK P) d lb x rb).val).all
              fun ps => !ps.isEmpty) &&
            ((xs.map fun x => (eager (K := DerivationKernel.over D K hK P) d lb x rb).val).any
              fun ps => ps.any Prod.isOpn)
        then [.opn lb rb] else [] := by
  have em := meetAll_val (P := P) K hK
  rw [← em]
  clear em
  at_cost K hK
  simp only [eager, Cost.bind_val, over_view, Charged.viewNode, Charged.op, h, Cost.pure_val,
    mapL_std, Cost.mapL_val]

end eager

end Unfold

end Tabled

end RwLog
