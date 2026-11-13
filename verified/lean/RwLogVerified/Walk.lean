/-
# Walking a term with the stack

A function that walks a term keeps on the stack of the store the frames it
has still to do. A `Visit` frame asks for a node to be done. A node that can
only be finished after its parts replaces its `Visit` frame by a `Build`
frame under one `Visit` frame for each part.

`Waits Kid done ent st` is what such a walk keeps true of its stack `st`. A
frame is read as a goal: its node and its second identifier. For every
`Build` frame:

* its node has no entry yet (`ent`);
* each part it waits for (`Kid`) is done or is the goal of a frame above it;
* every frame above it names an older node.

So when a `Build` frame is at the top its parts are done (`Waits.top`), and
no node is expanded twice: the frames above the `Build` frame of a node name
older nodes only, so none of them is that node.

`nV` and `nB` count the frames of each kind, for the tick bounds.
-/
import RwLogVerified.Repr

namespace RwLogVerified

open rwlog_core

/-- The node a frame names. -/
def fkey : store.Frame → Nat
  | .Visit q _ => q.val
  | .Build q _ => q.val

/-- The second identifier of a frame. -/
def faux : store.Frame → Nat
  | .Visit _ u => u.val
  | .Build _ u => u.val

/-- A frame as a goal. -/
def goal (f : store.Frame) : Nat × Nat := (fkey f, faux f)

def IsVisit : store.Frame → Prop
  | .Visit _ _ => True
  | .Build _ _ => False

/-- The number of `Visit` frames. -/
def nV : List store.Frame → Nat
  | [] => 0
  | .Visit _ _ :: st => nV st + 1
  | .Build _ _ :: st => nV st

/-- The number of `Build` frames. -/
def nB : List store.Frame → Nat
  | [] => 0
  | .Visit _ _ :: st => nB st
  | .Build _ _ :: st => nB st + 1

@[simp] theorem nV_nil : nV [] = 0 := rfl
@[simp] theorem nB_nil : nB [] = 0 := rfl
@[simp] theorem nV_visit (q u : store.TermId) (st : List store.Frame) :
    nV (.Visit q u :: st) = nV st + 1 := rfl
@[simp] theorem nV_build (q u : store.TermId) (st : List store.Frame) :
    nV (.Build q u :: st) = nV st := rfl
@[simp] theorem nB_visit (q u : store.TermId) (st : List store.Frame) :
    nB (.Visit q u :: st) = nB st := rfl
@[simp] theorem nB_build (q u : store.TermId) (st : List store.Frame) :
    nB (.Build q u :: st) = nB st + 1 := rfl

/-- What a walk keeps true of its stack. -/
def Waits (Kid : Nat × Nat → Nat × Nat → Prop) (done : Nat × Nat → Prop) (ent : Nat → Prop)
    (st : List store.Frame) : Prop :=
  ∀ pre q u post, st = pre ++ store.Frame.Build q u :: post →
    ¬ ent q.val ∧ (∀ c, Kid (q.val, u.val) c → done c ∨ ∃ f ∈ pre, goal f = c) ∧
      ∀ f ∈ pre, fkey f < q.val

variable {Kid : Nat × Nat → Nat × Nat → Prop} {done done' : Nat × Nat → Prop}
  {ent ent' : Nat → Prop}

theorem Waits.nil : Waits Kid done ent [] := by
  intro pre q u post h
  cases pre <;> simp at h

/-- A stack of one `Visit` frame. -/
theorem Waits.single (q u : store.TermId) : Waits Kid done ent [.Visit q u] := by
  intro pre q' u' post h
  rcases pre with _ | ⟨a, pre⟩
  · simp at h
  · simp only [List.cons_append, List.cons.injEq] at h
    have := h.2
    cases pre <;> simp at this

/-- The top frame is taken off, and its goal is done. More goals may be
done, and the only new entry is for the node of that frame. -/
theorem Waits.pop {f : store.Frame} {st : List store.Frame} (h : Waits Kid done ent (f :: st))
    (hd : ∀ g, done g → done' g) (hf : done' (goal f)) (he : ∀ k, ent' k → ent k ∨ k = fkey f) :
    Waits Kid done' ent' st := by
  intro pre q u post e
  obtain ⟨h1, h2, h3⟩ := h (f :: pre) q u post (by rw [e]; rfl)
  refine ⟨fun hq => ?_, fun c hc => ?_, fun f' hf' => h3 f' (List.mem_cons_of_mem _ hf')⟩
  · rcases he _ hq with h | h
    · exact h1 h
    · have := h3 f List.mem_cons_self
      omega
  · rcases h2 c hc with h | ⟨f', hf', e'⟩
    · exact Or.inl (hd c h)
    · rcases List.mem_cons.1 hf' with rfl | hf'
      · exact Or.inl (e' ▸ hf)
      · exact Or.inr ⟨f', hf', e'⟩

/-- A `Visit` frame is replaced by a `Build` frame under two `Visit` frames
for its parts. -/
theorem Waits.expand {q u : store.TermId} {f₁ f₂ : store.Frame} {st : List store.Frame}
    (h : Waits Kid done ent (.Visit q u :: st)) (hq : ¬ ent q.val)
    (hk : ∀ c, Kid (q.val, u.val) c → c = goal f₁ ∨ c = goal f₂)
    (h₁ : IsVisit f₁) (h₂ : IsVisit f₂) (l₁ : fkey f₁ < q.val) (l₂ : fkey f₂ < q.val) :
    Waits Kid done ent (f₁ :: f₂ :: .Build q u :: st) := by
  intro pre q' u' post e
  rcases pre with _ | ⟨a, _ | ⟨b, _ | ⟨c, pre⟩⟩⟩
  · simp only [List.nil_append, List.cons.injEq] at e
    rw [e.1] at h₁; exact h₁.elim
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
    rw [e.2.1] at h₂; exact h₂.elim
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, store.Frame.Build.injEq] at e
    obtain ⟨rfl, rfl, ⟨rfl, rfl⟩, -⟩ := e
    refine ⟨hq, fun c hc => Or.inr ?_, ?_⟩
    · rcases hk c hc with rfl | rfl
      · exact ⟨_, by simp, rfl⟩
      · exact ⟨_, by simp, rfl⟩
    · intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> assumption
  · simp only [List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl, rfl, e⟩ := e
    obtain ⟨g1, g2, g3⟩ := h (.Visit q u :: pre) q' u' post (by rw [e]; rfl)
    have hlt : q.val < q'.val := g3 (.Visit q u) List.mem_cons_self
    refine ⟨g1, fun c hc => ?_, ?_⟩
    · rcases g2 c hc with h | ⟨f', hf', e'⟩
      · exact Or.inl h
      · rcases List.mem_cons.1 hf' with rfl | hf'
        · exact Or.inr ⟨.Build q u, by simp, e'⟩
        · exact Or.inr ⟨f', by simp [hf'], e'⟩
    · intro f hf
      simp only [List.mem_cons] at hf
      rcases hf with rfl | rfl | rfl | hf
      · omega
      · omega
      · exact hlt
      · exact g3 f (List.mem_cons_of_mem _ hf)

/-- At the top, a `Build` frame has all its parts done and no entry. -/
theorem Waits.top {q u : store.TermId} {st : List store.Frame}
    (h : Waits Kid done ent (.Build q u :: st)) :
    ¬ ent q.val ∧ ∀ c, Kid (q.val, u.val) c → done c := by
  obtain ⟨h1, h2, -⟩ := h [] q u st rfl
  refine ⟨h1, fun c hc => ?_⟩
  rcases h2 c hc with h | ⟨f, hf, -⟩
  · exact h
  · simp at hf

/-- No frame above the `Build` frame of a node names that node. So a `Visit`
frame at the top names a node that has no `Build` frame. -/
theorem Waits.no_build {q u : store.TermId} {st : List store.Frame}
    (h : Waits Kid done ent (.Visit q u :: st)) :
    ∀ u', store.Frame.Build q u' ∉ st := by
  intro u' hm
  obtain ⟨pre, post, e⟩ := List.append_of_mem hm
  obtain ⟨-, -, h3⟩ := h (.Visit q u :: pre) q u' post (by rw [e]; rfl)
  have := h3 (.Visit q u) List.mem_cons_self
  simp only [fkey] at this
  omega

theorem Wf.nodesOK {s : store.Store} (h : Wf s) : NodesOK s.nodes.val :=
  ⟨h.root, h.shape.fits, h.shape.nodup⟩

/-- The identifier of the node a frame names. -/
def fid : store.Frame → store.TermId
  | .Visit q _ => q
  | .Build q _ => q

@[simp] theorem fid_val (f : store.Frame) : (fid f).val = fkey f := by cases f <;> rfl

theorem node_of_eq (f : store.Frame) : term.node_of f = .ok (fid f) := by
  cases f <;> rfl

end RwLogVerified
