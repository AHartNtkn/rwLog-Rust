/-
# The cursor of a push

A push keeps, for each answer it has pushed, how many answers of the table
opened for it are filed (`subs`), the answers filed (`reads`), and a cursor
over the pairs of an answer pushed and an answer filed for it. `PushOk` says
how the three fit: the reads are exactly the answers filed, each once for
every position below the count of its table, and the pairs to combine are
the reads not combined yet.

* `PushOk.start`, `PushOk.opened`, `PushOk.file`, `PushOk.mark`: the fit is
  kept by every unit of a push.
* `PushOk.next`: the pair a push takes is a read of an answer pushed, not
  combined before.
* `PushOk.done_of_todo`: when no pair is left, every read is combined.
-/
import RwLog.Rungs.Symmetric.Cursor
import RwLog.Rungs.Symmetric.PushFile

namespace RwLog.Symmetric

variable {S N A : Type}

/-- How many answers are filed for the answer pushed at `s`. -/
def cntOf (subs : List (A × Nat × Nat)) (s : Nat) : Nat :=
  match subs[s]? with
  | some e => e.2.2
  | none => 0

/-- The reads and the cursor fit the counts `cnt`: a read is of a position
below the count of its answer pushed, every such position is read, the pairs
combined are reads, and the pairs to combine are the reads not combined. -/
structure Filed (cnt : Nat → Nat) (reads : List (Nat × Nat)) (c : Cursor) : Prop where
  pb : c.pb.length = reads.length
  filed : ∀ q s r : Nat, reads[q]? = some (s, r) → r < cnt s
  all : ∀ s r : Nat, r < cnt s → ∃ q : Nat, reads[q]? = some (s, r)
  done : ∀ x ∈ c.done, ∃ r : Nat, reads[x.2]? = some (x.1, r)
  todo : ∀ x, x ∈ c.todo ↔ (∃ r : Nat, reads[x.2]? = some (x.1, r)) ∧ x ∉ c.done

/-- The answers pushed, the reads and the cursor of a push fit. -/
def PushOk (subs : List (A × Nat × Nat)) (reads : List (Nat × Nat)) (c : Cursor) : Prop :=
  c.pa.length = subs.length ∧ Filed (cntOf subs) reads c

theorem PushOk.start : PushOk ([] : List (A × Nat × Nat)) [] Cursor.start := by
  refine ⟨rfl, ⟨rfl, fun q s r h => ?_, fun s r h => ?_, fun x hx => ?_, fun x => ?_⟩⟩
  · simp at h
  · simp [cntOf] at h
  · cases hx
  · simp [Cursor.start]

theorem cntOf_append_zero (subs : List (A × Nat × Nat)) (x : A) (j : Nat) :
    cntOf (subs ++ [(x, j, 0)]) = cntOf subs := by
  funext s
  unfold cntOf
  rcases Nat.lt_trichotomy s subs.length with h | h | h
  · rw [List.getElem?_append_left h]
  · subst h
    simp
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- Pushing one more answer keeps the fit. -/
theorem PushOk.opened {subs : List (A × Nat × Nat)} {reads : List (Nat × Nat)} {c : Cursor}
    (h : PushOk subs reads c) (x : A) (j : Nat) (pth : Path) :
    PushOk (subs ++ [(x, j, 0)]) reads (c.opened pth) := by
  refine ⟨by simp [Cursor.opened, h.1], ?_⟩
  rw [cntOf_append_zero]
  exact ⟨h.2.pb, h.2.filed, h.2.all, h.2.done, h.2.todo⟩

/-- Filing one answer for the answer pushed at `s`. -/
theorem Filed.read {cnt : Nat → Nat} {reads : List (Nat × Nat)} {c : Cursor}
    (h : Filed cnt reads c) (s : Nat) (pth : Path) :
    Filed (Function.update cnt s (cnt s + 1)) (reads ++ [(s, cnt s)]) (c.read s pth) := by
  refine ⟨by simp [Cursor.read, h.pb], fun q s' r hq => ?_, fun s' r hr => ?_,
    fun x hx => ?_, fun x => ?_⟩
  · rcases Nat.lt_or_ge q reads.length with hl | hl
    · rw [List.getElem?_append_left hl] at hq
      have := h.filed q s' r hq
      by_cases e : s' = s
      · subst e; simp; omega
      · rw [Function.update_of_ne e]; exact this
    · rcases Nat.eq_or_lt_of_le hl with e | e
      · subst e
        simp only [List.getElem?_concat_length, Option.some.injEq, Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        simp
      · rw [List.getElem?_eq_none (by simp; omega)] at hq
        cases hq
  · by_cases e : s' = s
    · subst e
      simp only [Function.update_self] at hr
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hr' | rfl
      · obtain ⟨q, hq⟩ := h.all s' r hr'
        exact ⟨q, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hq).1]; exact hq⟩
      · exact ⟨reads.length, by simp⟩
    · rw [Function.update_of_ne e] at hr
      obtain ⟨q, hq⟩ := h.all s' r hr
      exact ⟨q, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hq).1]; exact hq⟩
  · obtain ⟨r, hr⟩ := h.done x hx
    exact ⟨r, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hr).1]; exact hr⟩
  · have ht : (c.read s pth).todo = c.todo ++ [(s, c.pb.length)] := rfl
    have hd : (c.read s pth).done = c.done := rfl
    rw [ht, hd, List.mem_append, h.todo x, List.mem_singleton, h.pb]
    constructor
    · rintro (⟨⟨r, hr⟩, hn⟩ | rfl)
      · exact ⟨⟨r, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hr).1]; exact hr⟩,
          hn⟩
      · refine ⟨⟨cnt s, by simp⟩, fun hx => ?_⟩
        obtain ⟨r, hr⟩ := h.done _ hx
        have := (List.getElem?_eq_some_iff.1 hr).1
        simp at this
    · rintro ⟨⟨r, hr⟩, hn⟩
      rcases Nat.lt_or_ge x.2 reads.length with hl | hl
      · rw [List.getElem?_append_left hl] at hr
        exact .inl ⟨⟨r, hr⟩, hn⟩
      · rcases Nat.eq_or_lt_of_le hl with e | e
        · rw [← e] at hr
          simp only [List.getElem?_concat_length, Option.some.injEq, Prod.mk.injEq] at hr
          exact .inr (Prod.ext hr.1.symm e.symm)
        · rw [List.getElem?_eq_none (by simp; omega)] at hr
          cases hr

/-- Filing the answers `pths` for the answer pushed at `s`. -/
theorem Filed.files (s : Nat) : ∀ (pths : List Path) (cnt : Nat → Nat)
    (reads : List (Nat × Nat)) (c : Cursor), Filed cnt reads c →
    Filed (Function.update cnt s (cnt s + pths.length)) (fileReads s (cnt s) reads c pths).1
      (fileReads s (cnt s) reads c pths).2
  | [], cnt, reads, c, h => by simpa [fileReads] using h
  | pth :: rest, cnt, reads, c, h => by
    have h1 := h.read s pth
    have h2 := Filed.files s rest _ _ _ h1
    simp only [Function.update_self, Function.update_idem] at h2
    simp only [fileReads, List.length_cons]
    rw [show cnt s + (rest.length + 1) = cnt s + 1 + rest.length by omega]
    exact h2

theorem fileReads_pa (s : Nat) : ∀ (pths : List Path) (n : Nat) (reads : List (Nat × Nat))
    (c : Cursor), (fileReads s n reads c pths).2.pa = c.pa
  | [], _, _, _ => rfl
  | _ :: rest, _, _, _ => by rw [fileReads, fileReads_pa s rest]; rfl

theorem pushFile_pa (st : StateOf S N A) : ∀ (subs : List (A × Nat × Nat)) (s : Nat)
    (reads : List (Nat × Nat)) (c : Cursor), (pushFile st s reads c subs).2.2.pa = c.pa
  | [], _, _, _ => rfl
  | e :: rest, s, reads, c => by
    simp only [pushFile]
    rw [pushFile_pa st rest, fileReads_pa]

theorem cntOf_update (pre rest : List (A × Nat × Nat)) (e : A × Nat × Nat) (n : Nat) :
    Function.update (cntOf (pre ++ e :: rest)) pre.length n =
      cntOf ((pre ++ [(e.1, e.2.1, n)]) ++ rest) := by
  funext s
  unfold cntOf
  rcases Nat.lt_trichotomy s pre.length with h | h | h
  · rw [Function.update_of_ne (by omega), List.append_assoc, List.getElem?_append_left h,
      List.getElem?_append_left h]
  · subst h
    simp
  · rw [Function.update_of_ne (by omega), List.append_assoc,
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    obtain ⟨d, rfl⟩ : ∃ d, s = pre.length + 1 + d := ⟨s - pre.length - 1, by omega⟩
    simp [show pre.length + 1 + d - pre.length = d + 1 by omega]

/-- Filing the answers the tables of a push have gained keeps the fit. -/
theorem Filed.push (st : StateOf S N A) : ∀ (rest pre : List (A × Nat × Nat))
    (reads : List (Nat × Nat)) (c : Cursor), Filed (cntOf (pre ++ rest)) reads c →
    (∀ e ∈ rest, e.2.2 ≤ (st.pathsAt e.2.1).length) →
    Filed (cntOf (pre ++ (pushFile st pre.length reads c rest).1))
      (pushFile st pre.length reads c rest).2.1 (pushFile st pre.length reads c rest).2.2
  | [], pre, reads, c, h, _ => by simpa [pushFile] using h
  | e :: rest, pre, reads, c, h, hle => by
    have hc : cntOf (pre ++ e :: rest) pre.length = e.2.2 := by simp [cntOf]
    have h1 := Filed.files pre.length ((st.pathsAt e.2.1).drop e.2.2) _ _ _ h
    rw [hc, List.length_drop,
      show e.2.2 + ((st.pathsAt e.2.1).length - e.2.2) = (st.pathsAt e.2.1).length from by
        have := hle e List.mem_cons_self
        omega, cntOf_update] at h1
    have h2 := Filed.push st rest (pre ++ [(e.1, e.2.1, (st.pathsAt e.2.1).length)]) _ _ h1
      fun e' he' => hle e' (List.mem_cons_of_mem _ he')
    simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
      List.cons_append, List.nil_append] at h2
    simpa [pushFile] using h2

/-- Filing keeps the fit of a push. -/
theorem PushOk.file {subs : List (A × Nat × Nat)} {reads : List (Nat × Nat)} {c : Cursor}
    (h : PushOk subs reads c) (st : StateOf S N A)
    (hle : ∀ e ∈ subs, e.2.2 ≤ (st.pathsAt e.2.1).length) :
    PushOk (pushFile st 0 reads c subs).1 (pushFile st 0 reads c subs).2.1
      (pushFile st 0 reads c subs).2.2 := by
  refine ⟨by rw [pushFile_pa, pushFile_length]; exact h.1, ?_⟩
  simpa using Filed.push st subs [] reads c (by simpa using h.2) hle

/-- The pair a push takes: a read of an answer pushed, not combined
before. -/
theorem PushOk.next {subs : List (A × Nat × Nat)} {reads : List (Nat × Nat)} {c : Cursor}
    (h : PushOk subs reads c) {p : Nat × Nat} (hp : c.next = some p) :
    ∃ e r, subs[p.1]? = some e ∧ reads[p.2]? = some (p.1, r) ∧ r < e.2.2 ∧
      ¬ c.Before p.1 p.2 := by
  obtain ⟨⟨r, hr⟩, hn⟩ := (h.2.todo p).1 (Cursor.next_todo hp)
  have hlt := h.2.filed _ _ _ hr
  unfold cntOf at hlt
  cases he : subs[p.1]? with
  | none => rw [he] at hlt; cases hlt
  | some e => rw [he] at hlt; exact ⟨e, r, rfl, hr, hlt, hn⟩

/-- Marking the pair taken keeps the fit. -/
theorem PushOk.mark {subs : List (A × Nat × Nat)} {reads : List (Nat × Nat)} {c : Cursor}
    (h : PushOk subs reads c) {p : Nat × Nat} (hp : c.next = some p) (t : Nat) :
    PushOk subs reads (c.mark p t) := by
  have hm := (h.2.todo p).1 (Cursor.next_todo hp)
  refine ⟨h.1, ⟨h.2.pb, h.2.filed, h.2.all, fun x hx => ?_, fun x => ?_⟩⟩
  · simp only [Cursor.mark, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hm.1
    · exact h.2.done x hx
  · simp only [Cursor.mark, List.mem_filter, List.mem_cons, bne_iff_ne, ne_eq, not_or]
    rw [h.2.todo x]
    constructor
    · rintro ⟨⟨hf, hd⟩, hne⟩
      exact ⟨hf, hne, hd⟩
    · rintro ⟨hf, hne, hd⟩
      exact ⟨⟨hf, hd⟩, hne⟩

/-- When no pair is left to combine, every read is combined. -/
theorem PushOk.done_of_todo {subs : List (A × Nat × Nat)} {reads : List (Nat × Nat)}
    {c : Cursor} (h : PushOk subs reads c) (ht : c.todo = []) {q s r : Nat}
    (hq : reads[q]? = some (s, r)) : c.Before s q := by
  by_contra hn
  have : (s, q) ∈ c.todo := (h.2.todo (s, q)).2 ⟨⟨r, hq⟩, hn⟩
  rw [ht] at this
  cases this

end RwLog.Symmetric
