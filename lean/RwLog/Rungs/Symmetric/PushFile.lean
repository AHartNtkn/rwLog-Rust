/-
# Filing the units of a push

`seeSide` files the answers the side of a push has gained, each with the unit
that opens its goal. `pushFile` files the answers that the tables opened by a
push have gained, but for the answers superseded. Neither takes a unit: the
answers seen stay, with their tables, and only how many answers of each table
are filed changes.
-/
import RwLog.Rungs.Symmetric.Machine

namespace RwLog.Symmetric

variable {S N A : Type}

/-- Seeing answers of the side adds them, unopened, after the answers
seen. -/
theorem seeSide_subs : ∀ (new : List (A × Path)) (subs : List (A × Option (Nat × Nat)))
    (reads : List (Nat × Option Nat)) (c : Cursor),
    (seeSide new subs reads c).1 = subs ++ new.map fun x => (x.1, none)
  | [], subs, _, _ => by simp [seeSide]
  | x :: rest, subs, reads, c => by
    rw [seeSide, seeSide_subs rest]
    simp

theorem seeSide_done : ∀ (new : List (A × Path)) (subs : List (A × Option (Nat × Nat)))
    (reads : List (Nat × Option Nat)) (c : Cursor), (seeSide new subs reads c).2.2.done = c.done
  | [], _, _, _ => rfl
  | x :: rest, subs, reads, c => by rw [seeSide, seeSide_done rest]; rfl

theorem seeSide_prefix : ∀ (new : List (A × Path)) (subs : List (A × Option (Nat × Nat)))
    (reads : List (Nat × Option Nat)) (c : Cursor), reads <+: (seeSide new subs reads c).2.1
  | [], _, _, _ => List.prefix_rfl
  | x :: rest, subs, reads, c => by
    rw [seeSide]
    exact (List.prefix_append _ _).trans (seeSide_prefix rest _ _ _)

/-- Filing keeps each answer seen and its table, and files every answer of
the table, unless the answer is superseded. -/
theorem pushFile_getElem? (st : StateOf S N A) (dead : List Nat) :
    ∀ (subs : List (A × Option (Nat × Nat))) (s : Nat) (reads : List (Nat × Option Nat))
      (c : Cursor) (n : Nat),
      (pushFile st dead s reads c subs).1[n]? =
        subs[n]?.map fun e => (e.1, e.2.map fun t =>
          (t.1, if dead.contains (s + n) then t.2 else (st.pathsAt t.1).length))
  | [], _, _, _, _ => by simp [pushFile]
  | (x, none) :: rest, s, reads, c, n => by
    cases n with
    | zero => simp [pushFile]
    | succ n =>
      simp only [pushFile, List.getElem?_cons_succ]
      rw [pushFile_getElem? st dead rest, show s + 1 + n = s + (n + 1) by omega]
  | (x, some t) :: rest, s, reads, c, n => by
    rw [pushFile]
    split
    · next hd =>
      cases n with
      | zero =>
        have hd' := hd
        rw [List.contains_iff_mem] at hd'
        simp [hd']
      | succ n =>
        simp only [List.getElem?_cons_succ]
        rw [pushFile_getElem? st dead rest, show s + 1 + n = s + (n + 1) by omega]
    · next hd =>
      cases n with
      | zero =>
        have hd' := hd
        rw [List.contains_iff_mem] at hd'
        simp [hd']
      | succ n =>
        simp only [List.getElem?_cons_succ]
        rw [pushFile_getElem? st dead rest, show s + 1 + n = s + (n + 1) by omega]

theorem pushFile_length (st : StateOf S N A) (dead : List Nat) :
    ∀ (subs : List (A × Option (Nat × Nat))) (s : Nat) (reads : List (Nat × Option Nat))
      (c : Cursor), (pushFile st dead s reads c subs).1.length = subs.length
  | [], _, _, _ => by simp [pushFile]
  | (x, none) :: rest, s, reads, c => by simp [pushFile, pushFile_length st dead rest]
  | (x, some t) :: rest, s, reads, c => by
    rw [pushFile]
    split <;> simp [pushFile_length st dead rest]

theorem fileReads_done (s : Nat) : ∀ (pths : List Path) (n : Nat)
    (reads : List (Nat × Option Nat)) (c : Cursor), (fileReads s n reads c pths).2.done = c.done
  | [], _, _, _ => rfl
  | _ :: rest, _, _, _ => by rw [fileReads, fileReads_done s rest]; rfl

theorem fileReads_prefix (s : Nat) : ∀ (pths : List Path) (n : Nat)
    (reads : List (Nat × Option Nat)) (c : Cursor), reads <+: (fileReads s n reads c pths).1
  | [], _, _, _ => List.prefix_rfl
  | _ :: rest, _, _, _ => by
    rw [fileReads]
    exact (List.prefix_append _ _).trans (fileReads_prefix s rest _ _ _)

/-- Filing takes no unit. -/
theorem pushFile_done (st : StateOf S N A) (dead : List Nat) :
    ∀ (subs : List (A × Option (Nat × Nat))) (s : Nat) (reads : List (Nat × Option Nat))
      (c : Cursor), (pushFile st dead s reads c subs).2.2.done = c.done
  | [], _, _, _ => rfl
  | (x, none) :: rest, s, reads, c => by
    simp only [pushFile]
    rw [pushFile_done st dead rest]
  | (x, some t) :: rest, s, reads, c => by
    rw [pushFile]
    split
    · exact pushFile_done st dead rest _ _ _
    · exact (pushFile_done st dead rest _ _ _).trans (fileReads_done _ _ _ _ _)

/-- Filing keeps the units there were. -/
theorem pushFile_prefix (st : StateOf S N A) (dead : List Nat) :
    ∀ (subs : List (A × Option (Nat × Nat))) (s : Nat) (reads : List (Nat × Option Nat))
      (c : Cursor), reads <+: (pushFile st dead s reads c subs).2.1
  | [], _, _, _ => List.prefix_rfl
  | (x, none) :: rest, s, reads, c => by
    simp only [pushFile]
    exact pushFile_prefix st dead rest _ _ _
  | (x, some t) :: rest, s, reads, c => by
    rw [pushFile]
    split
    · exact pushFile_prefix st dead rest _ _ _
    · exact (fileReads_prefix _ _ _ _ _).trans (pushFile_prefix st dead rest _ _ _)

end RwLog.Symmetric
