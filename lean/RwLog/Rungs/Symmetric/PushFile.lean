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

theorem fileReads_done (s : Nat) : ∀ (pths : List Path) (n : Nat) (reads : List (Nat × Nat))
    (c : Cursor), (fileReads s n reads c pths).2.done = c.done
  | [], _, _, _ => rfl
  | _ :: rest, _, _, _ => by rw [fileReads, fileReads_done s rest]; rfl

theorem fileReads_prefix (s : Nat) : ∀ (pths : List Path) (n : Nat) (reads : List (Nat × Nat))
    (c : Cursor), reads <+: (fileReads s n reads c pths).1
  | [], _, _, _ => List.prefix_rfl
  | _ :: rest, _, _, _ => by
    rw [fileReads]
    exact (List.prefix_append _ _).trans (fileReads_prefix s rest _ _ _)

/-- Filing combines nothing. -/
theorem pushFile_done (st : StateOf S N A) : ∀ (subs : List (A × Nat × Nat)) (s : Nat)
    (reads : List (Nat × Nat)) (c : Cursor), (pushFile st s reads c subs).2.2.done = c.done
  | [], _, _, _ => rfl
  | e :: rest, s, reads, c => by
    simp only [pushFile]
    rw [pushFile_done st rest, fileReads_done]

/-- Filing keeps the reads there were. -/
theorem pushFile_prefix (st : StateOf S N A) : ∀ (subs : List (A × Nat × Nat)) (s : Nat)
    (reads : List (Nat × Nat)) (c : Cursor), reads <+: (pushFile st s reads c subs).2.1
  | [], _, _, _ => List.prefix_rfl
  | e :: rest, s, reads, c => by
    simp only [pushFile]
    exact (fileReads_prefix _ _ _ _ _).trans (pushFile_prefix st rest _ _ _)

end RwLog.Symmetric
