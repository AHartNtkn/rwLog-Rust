/-
# Filing the answers a push reads

`pushFile` files the answers that the tables opened by a push have gained.
It changes neither the answers pushed nor their tables, only how many answers
of each table are filed.
-/
import RwLog.Rungs.Symmetric.Machine

namespace RwLog.Symmetric

variable {S N A : Type}

/-- Filing keeps each answer pushed and its table, and files every answer of
the table. -/
theorem pushFile_getElem? (st : StateOf S N A) :
    ∀ (subs : List (A × Nat × Nat)) (s : Nat) (reads : List (Nat × Nat)) (c : Cursor) (n : Nat),
      (pushFile st s reads c subs).1[n]? =
        subs[n]?.map fun e => (e.1, e.2.1, (st.pathsAt e.2.1).length)
  | [], _, _, _, _ => by simp [pushFile]
  | e :: rest, s, reads, c, n => by
    cases n with
    | zero => simp [pushFile]
    | succ n => simpa [pushFile] using pushFile_getElem? st rest _ _ _ n

theorem pushFile_length (st : StateOf S N A) (subs : List (A × Nat × Nat)) (s : Nat)
    (reads : List (Nat × Nat)) (c : Cursor) :
    (pushFile st s reads c subs).1.length = subs.length := by
  induction subs generalizing s reads c with
  | nil => simp [pushFile]
  | cons e rest ih => simp [pushFile, ih]

/-- Filing keeps the answers pushed and their tables. -/
theorem pushFile_map (st : StateOf S N A) (subs : List (A × Nat × Nat)) (s : Nat)
    (reads : List (Nat × Nat)) (c : Cursor) :
    (pushFile st s reads c subs).1.map (fun e => (e.1, e.2.1)) =
      subs.map fun e => (e.1, e.2.1) := by
  induction subs generalizing s reads c with
  | nil => simp [pushFile]
  | cons e rest ih => simp [pushFile, ih]

end RwLog.Symmetric
