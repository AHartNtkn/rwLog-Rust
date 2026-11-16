/-
# The cursor of a push

A push keeps the answers of its side it has seen, each with the table opened
for it once it is opened and how many answers of that table are filed
(`subs`); the units filed (`reads`): for each answer seen the unit that opens
its goal, and for each answer filed of an opened table the unit that combines
it; and a cursor over the units. `PushFits` says how the three fit: the units
are exactly these, each once, an answer is opened exactly when its opening
unit is taken, and the units to take are the units not taken yet.

* `PushFits.start`, `PushFits.see`, `PushFits.file`, `PushFits.markOpen`,
  `PushFits.markRead`: the fit is kept by everything a push does.
* `PushFits.next`: the unit a push takes opens an answer not opened, or
  combines an answer of an opened table, and was not taken before.
* `PushFits.done_of_todo`: when no unit is left, every answer seen is opened
  and every answer filed is combined.
-/
import RwLog.Rungs.Symmetric.Cursor
import RwLog.Rungs.Symmetric.PushFile

namespace RwLog.Symmetric

variable {S N A : Type}

/-- How many answers are filed for the answer seen at `s`. -/
def cntOf (subs : List (A × Option (Nat × Nat))) (s : Nat) : Nat :=
  match subs[s]? with
  | some (_, some t) => t.2
  | _ => 0

/-- The goal of the answer seen at `s` is opened. -/
def IsOpen (subs : List (A × Option (Nat × Nat))) (s : Nat) : Prop :=
  ∃ x t, subs[s]? = some (x, some t)

/-- The units and the cursor fit `n` answers seen, of which `opened` are
opened, with the counts `cnt` of answers filed. -/
structure Filed (n : Nat) (opened : Nat → Prop) (cnt : Nat → Nat)
    (reads : List (Nat × Option Nat)) (c : Cursor) : Prop where
  pb : c.pb.length = reads.length
  filed : ∀ q s r : Nat, reads[q]? = some (s, some r) → r < cnt s
  all : ∀ s r : Nat, r < cnt s → ∃ q : Nat, reads[q]? = some (s, some r)
  seen : ∀ q s : Nat, reads[q]? = some (s, none) → s < n
  opens : ∀ s : Nat, s < n → ∃ q : Nat, reads[q]? = some (s, none)
  once : ∀ q q' s : Nat, reads[q]? = some (s, none) → reads[q']? = some (s, none) → q = q'
  isOpen : ∀ q s : Nat, reads[q]? = some (s, none) → ((s, q) ∈ c.done ↔ opened s)
  done : ∀ x ∈ c.done, ∃ r : Option Nat, reads[x.2]? = some (x.1, r)
  todo : ∀ x, x ∈ c.todo ↔ (∃ r : Option Nat, reads[x.2]? = some (x.1, r)) ∧ x ∉ c.done

/-- The answers seen, the units and the cursor of a push fit. -/
def PushFits (subs : List (A × Option (Nat × Nat))) (reads : List (Nat × Option Nat))
    (c : Cursor) : Prop :=
  c.pa.length = subs.length ∧ Filed subs.length (IsOpen subs) (cntOf subs) reads c

theorem Filed.congr {n : Nat} {o o' : Nat → Prop} {cnt cnt' : Nat → Nat}
    {reads : List (Nat × Option Nat)} {c : Cursor} (h : Filed n o cnt reads c)
    (ho : ∀ s, o s ↔ o' s) (hc : cnt = cnt') : Filed n o' cnt' reads c := by
  subst hc
  exact ⟨h.pb, h.filed, h.all, h.seen, h.opens, h.once,
    fun q s hq => (h.isOpen q s hq).trans (ho s), h.done, h.todo⟩

theorem PushFits.start : PushFits ([] : List (A × Option (Nat × Nat))) [] Cursor.start := by
  refine ⟨rfl, ⟨rfl, fun q s r h => ?_, fun s r h => ?_, fun q s h => ?_, fun s h => ?_,
    fun q q' s h => ?_, fun q s h => ?_, fun x hx => ?_, fun x => ?_⟩⟩
  · simp at h
  · simp [cntOf] at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · cases hx
  · simp [Cursor.start]

/-- An entry of a list with one more at its end is an entry of the list, or
the one more. -/
theorem getElem?_concat_cases {α : Type} {l : List α} {a b : α} {q : Nat}
    (h : (l ++ [a])[q]? = some b) : l[q]? = some b ∨ (q = l.length ∧ a = b) := by
  rcases Nat.lt_trichotomy q l.length with hl | hl | hl
  · rw [List.getElem?_append_left hl] at h
    exact .inl h
  · subst hl
    simp only [List.getElem?_concat_length, Option.some.injEq] at h
    exact .inr ⟨rfl, h⟩
  · rw [List.getElem?_eq_none (by simp; omega)] at h
    cases h

theorem getElem?_concat_of {α : Type} {l : List α} {a b : α} {q : Nat} (h : l[q]? = some b) :
    (l ++ [a])[q]? = some b := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

theorem lt_of_getElem? {α : Type} {l : List α} {b : α} {q : Nat} (h : l[q]? = some b) :
    q < l.length := (List.getElem?_eq_some_iff.1 h).1

/-- The units to take once one more unit is filed. -/
theorem todo_read {n : Nat} {o : Nat → Prop} {cnt : Nat → Nat}
    {reads : List (Nat × Option Nat)} {c : Cursor} (h : Filed n o cnt reads c) (s : Nat)
    (pth : Path) (r : Option Nat) (x : Nat × Nat) :
    x ∈ (c.read s pth).todo ↔
      (∃ r' : Option Nat, (reads ++ [(s, r)])[x.2]? = some (x.1, r')) ∧ x ∉ (c.read s pth).done := by
  have ht : (c.read s pth).todo = c.todo ++ [(s, c.pb.length)] := rfl
  have hd : (c.read s pth).done = c.done := rfl
  rw [ht, hd, List.mem_append, h.todo x, List.mem_singleton, h.pb]
  constructor
  · rintro (⟨⟨r', hr⟩, hn⟩ | rfl)
    · exact ⟨⟨r', getElem?_concat_of hr⟩, hn⟩
    · refine ⟨⟨r, by simp⟩, fun hx => ?_⟩
      obtain ⟨r', hr⟩ := h.done _ hx
      have := lt_of_getElem? hr
      simp at this
  · rintro ⟨⟨r', hr⟩, hn⟩
    rcases getElem?_concat_cases hr with hr | ⟨e, hr⟩
    · exact .inl ⟨⟨r', hr⟩, hn⟩
    · simp only [Prod.mk.injEq] at hr
      exact .inr (Prod.ext hr.1.symm e)

/-- Filing one answer for the answer seen at `s`. -/
theorem Filed.read {n : Nat} {o : Nat → Prop} {cnt : Nat → Nat}
    {reads : List (Nat × Option Nat)} {c : Cursor} (h : Filed n o cnt reads c) (s : Nat)
    (pth : Path) :
    Filed n o (Function.update cnt s (cnt s + 1)) (reads ++ [(s, some (cnt s))])
      (c.read s pth) := by
  refine ⟨by simp [Cursor.read, h.pb], fun q s' r hq => ?_, fun s' r hr => ?_,
    fun q s' hq => ?_, fun s' hs => ?_, fun q q' s' hq hq' => ?_, fun q s' hq => ?_,
    fun x hx => ?_, todo_read h s pth _⟩
  · rcases getElem?_concat_cases hq with hq | ⟨-, hq⟩
    · have := h.filed q s' r hq
      by_cases e : s' = s
      · subst e; simp; omega
      · rw [Function.update_of_ne e]; exact this
    · simp only [Prod.mk.injEq, Option.some.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      simp
  · by_cases e : s' = s
    · subst e
      simp only [Function.update_self] at hr
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hr' | rfl
      · obtain ⟨q, hq⟩ := h.all s' r hr'
        exact ⟨q, getElem?_concat_of hq⟩
      · exact ⟨reads.length, by simp⟩
    · rw [Function.update_of_ne e] at hr
      obtain ⟨q, hq⟩ := h.all s' r hr
      exact ⟨q, getElem?_concat_of hq⟩
  · rcases getElem?_concat_cases hq with hq | ⟨-, hq⟩
    · exact h.seen q s' hq
    · simp at hq
  · obtain ⟨q, hq⟩ := h.opens s' hs
    exact ⟨q, getElem?_concat_of hq⟩
  · rcases getElem?_concat_cases hq with hq | ⟨-, hq⟩
    · rcases getElem?_concat_cases hq' with hq' | ⟨-, hq'⟩
      · exact h.once q q' s' hq hq'
      · simp at hq'
    · simp at hq
  · rcases getElem?_concat_cases hq with hq | ⟨-, hq⟩
    · exact h.isOpen q s' hq
    · simp at hq
  · obtain ⟨r, hr⟩ := h.done x hx
    exact ⟨r, getElem?_concat_of hr⟩

/-- Seeing one more answer of the side: the unit that opens its goal is
filed. -/
theorem Filed.see {n : Nat} {o : Nat → Prop} {cnt : Nat → Nat}
    {reads : List (Nat × Option Nat)} {c : Cursor} (h : Filed n o cnt reads c) (hn : ¬ o n)
    (pth : Path) :
    Filed (n + 1) o cnt (reads ++ [(n, none)]) ((c.opened pth).read n []) := by
  have h' : Filed n o cnt reads (c.opened pth) :=
    ⟨h.pb, h.filed, h.all, h.seen, h.opens, h.once, h.isOpen, h.done, h.todo⟩
  refine ⟨by simp [Cursor.read, Cursor.opened, h.pb], fun q s' r hq => ?_, fun s' r hr => ?_,
    fun q s' hq => ?_, fun s' hs => ?_, fun q q' s' hq hq' => ?_, fun q s' hq => ?_,
    fun x hx => ?_, todo_read h' n [] _⟩
  · rcases getElem?_concat_cases hq with hq | ⟨-, hq⟩
    · exact h.filed q s' r hq
    · simp at hq
  · obtain ⟨q, hq⟩ := h.all s' r hr
    exact ⟨q, getElem?_concat_of hq⟩
  · rcases getElem?_concat_cases hq with hq | ⟨-, hq⟩
    · exact Nat.lt_succ_of_lt (h.seen q s' hq)
    · simp only [Prod.mk.injEq, and_true] at hq
      omega
  · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs) with hs | rfl
    · obtain ⟨q, hq⟩ := h.opens s' hs
      exact ⟨q, getElem?_concat_of hq⟩
    · exact ⟨reads.length, by simp⟩
  · rcases getElem?_concat_cases hq with hq | ⟨e, hq⟩
    · rcases getElem?_concat_cases hq' with hq' | ⟨e', hq'⟩
      · exact h.once q q' s' hq hq'
      · simp only [Prod.mk.injEq, and_true] at hq'
        have := h.seen q s' hq
        omega
    · rcases getElem?_concat_cases hq' with hq' | ⟨e', hq'⟩
      · simp only [Prod.mk.injEq, and_true] at hq
        have := h.seen q' s' hq'
        omega
      · omega
  · rcases getElem?_concat_cases hq with hq | ⟨e, hq⟩
    · exact h.isOpen q s' hq
    · simp only [Prod.mk.injEq, and_true] at hq
      subst hq
      subst e
      constructor
      · intro hd
        obtain ⟨r, hr⟩ := h.done _ hd
        have := lt_of_getElem? hr
        simp at this
      · intro ho
        exact absurd ho hn
  · obtain ⟨r, hr⟩ := h.done x hx
    exact ⟨r, getElem?_concat_of hr⟩

theorem cntOf_append_none (subs : List (A × Option (Nat × Nat))) (x : A) :
    cntOf (subs ++ [(x, none)]) = cntOf subs := by
  funext s
  unfold cntOf
  rcases Nat.lt_trichotomy s subs.length with h | h | h
  · rw [List.getElem?_append_left h]
  · subst h
    simp
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem isOpen_append_none (subs : List (A × Option (Nat × Nat))) (x : A) (s : Nat) :
    IsOpen subs s ↔ IsOpen (subs ++ [(x, none)]) s := by
  unfold IsOpen
  rcases Nat.lt_trichotomy s subs.length with h | h | h
  · rw [List.getElem?_append_left h]
  · subst h
    simp
  · rw [List.getElem?_eq_none (show subs.length ≤ s by omega),
      List.getElem?_eq_none (show (subs ++ [(x, none)]).length ≤ s by
        simp only [List.length_append, List.length_singleton]; omega)]

theorem not_isOpen_length (subs : List (A × Option (Nat × Nat))) : ¬ IsOpen subs subs.length := by
  rintro ⟨x, t, h⟩
  simp at h

/-- Seeing one more answer of the side keeps the fit. -/
theorem PushFits.see {subs : List (A × Option (Nat × Nat))} {reads : List (Nat × Option Nat)}
    {c : Cursor} (h : PushFits subs reads c) (x : A) (pth : Path) :
    PushFits (subs ++ [(x, none)]) (reads ++ [(subs.length, none)])
      ((c.opened pth).read subs.length []) := by
  refine ⟨by simp [Cursor.read, Cursor.opened, h.1], ?_⟩
  rw [List.length_append, List.length_singleton]
  exact (h.2.see (not_isOpen_length subs) pth).congr (isOpen_append_none subs x)
    (cntOf_append_none subs x).symm

/-- Seeing the answers the side has gained keeps the fit. -/
theorem PushFits.seeSide : ∀ (new : List (A × Path)) {subs : List (A × Option (Nat × Nat))}
    {reads : List (Nat × Option Nat)} {c : Cursor}, PushFits subs reads c →
    PushFits (seeSide new subs reads c).1 (seeSide new subs reads c).2.1
      (seeSide new subs reads c).2.2
  | [], _, _, _, h => h
  | x :: rest, _, _, _, h => by
    rw [RwLog.Symmetric.seeSide]
    exact PushFits.seeSide rest (h.see x.1 x.2)

/-- Filing the answers `pths` for the answer seen at `s`. -/
theorem Filed.files {n : Nat} {o : Nat → Prop} (s : Nat) : ∀ (pths : List Path)
    (cnt : Nat → Nat) (reads : List (Nat × Option Nat)) (c : Cursor), Filed n o cnt reads c →
    Filed n o (Function.update cnt s (cnt s + pths.length)) (fileReads s (cnt s) reads c pths).1
      (fileReads s (cnt s) reads c pths).2
  | [], cnt, reads, c, h => by simpa [fileReads] using h
  | pth :: rest, cnt, reads, c, h => by
    have h1 := h.read s pth
    have h2 := Filed.files s rest _ _ _ h1
    simp only [Function.update_self, Function.update_idem] at h2
    simp only [fileReads, List.length_cons]
    rw [show cnt s + (rest.length + 1) = cnt s + 1 + rest.length by omega]
    exact h2

theorem fileReads_pa (s : Nat) : ∀ (pths : List Path) (n : Nat)
    (reads : List (Nat × Option Nat)) (c : Cursor), (fileReads s n reads c pths).2.pa = c.pa
  | [], _, _, _ => rfl
  | _ :: rest, _, _, _ => by rw [fileReads, fileReads_pa s rest]; rfl

theorem pushFile_pa (st : StateOf S N A) : ∀ (subs : List (A × Option (Nat × Nat))) (s : Nat)
    (reads : List (Nat × Option Nat)) (c : Cursor), (pushFile st s reads c subs).2.2.pa = c.pa
  | [], _, _, _ => rfl
  | (x, none) :: rest, s, reads, c => by
    simp only [pushFile]
    rw [pushFile_pa st rest]
  | (x, some t) :: rest, s, reads, c => by
    simp only [pushFile]
    rw [pushFile_pa st rest, fileReads_pa]

theorem cntOf_update (pre rest : List (A × Option (Nat × Nat))) (x : A) (t : Nat × Nat)
    (n : Nat) :
    Function.update (cntOf (pre ++ (x, some t) :: rest)) pre.length n =
      cntOf ((pre ++ [(x, some (t.1, n))]) ++ rest) := by
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
theorem Filed.push {n : Nat} {o : Nat → Prop} (st : StateOf S N A) :
    ∀ (rest pre : List (A × Option (Nat × Nat))) (reads : List (Nat × Option Nat))
      (c : Cursor), Filed n o (cntOf (pre ++ rest)) reads c →
    (∀ e ∈ rest, ∀ t, e.2 = some t → t.2 ≤ (st.pathsAt t.1).length) →
    Filed n o (cntOf (pre ++ (pushFile st pre.length reads c rest).1))
      (pushFile st pre.length reads c rest).2.1 (pushFile st pre.length reads c rest).2.2
  | [], pre, reads, c, h, _ => by simpa [pushFile] using h
  | (x, none) :: rest, pre, reads, c, h, hle => by
    have h1 : Filed n o (cntOf ((pre ++ [(x, none)]) ++ rest)) reads c := by
      simpa using h
    have h2 := Filed.push st rest (pre ++ [(x, none)]) _ _ h1
      fun e' he' => hle e' (List.mem_cons_of_mem _ he')
    simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
      List.cons_append, List.nil_append] at h2
    simpa [pushFile] using h2
  | (x, some t) :: rest, pre, reads, c, h, hle => by
    have hc : cntOf (pre ++ (x, some t) :: rest) pre.length = t.2 := by simp [cntOf]
    have h1 := Filed.files pre.length ((st.pathsAt t.1).drop t.2) _ _ _ h
    rw [hc, List.length_drop,
      show t.2 + ((st.pathsAt t.1).length - t.2) = (st.pathsAt t.1).length from by
        have := hle _ List.mem_cons_self t rfl
        omega, cntOf_update] at h1
    have h2 := Filed.push st rest (pre ++ [(x, some (t.1, (st.pathsAt t.1).length))]) _ _ h1
      fun e' he' => hle e' (List.mem_cons_of_mem _ he')
    simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
      List.cons_append, List.nil_append] at h2
    simpa [pushFile] using h2

theorem isOpen_pushFile (st : StateOf S N A) (subs : List (A × Option (Nat × Nat)))
    (reads : List (Nat × Option Nat)) (c : Cursor) (s : Nat) :
    IsOpen subs s ↔ IsOpen (pushFile st 0 reads c subs).1 s := by
  unfold IsOpen
  rw [pushFile_getElem?]
  cases subs[s]? with
  | none => simp
  | some e =>
    rcases e with ⟨x, _ | t⟩
    · simp
    · simp

/-- Filing keeps the fit of a push. -/
theorem PushFits.file {subs : List (A × Option (Nat × Nat))} {reads : List (Nat × Option Nat)}
    {c : Cursor} (h : PushFits subs reads c) (st : StateOf S N A)
    (hle : ∀ e ∈ subs, ∀ t, e.2 = some t → t.2 ≤ (st.pathsAt t.1).length) :
    PushFits (pushFile st 0 reads c subs).1 (pushFile st 0 reads c subs).2.1
      (pushFile st 0 reads c subs).2.2 := by
  refine ⟨by rw [pushFile_pa, pushFile_length]; exact h.1, ?_⟩
  rw [pushFile_length]
  have := Filed.push (n := subs.length) (o := IsOpen subs) st subs [] reads c
    (by simpa using h.2) hle
  exact Filed.congr (by simpa using this) (isOpen_pushFile st subs reads c) rfl

/-- The unit a push takes: it opens an answer seen that is not opened, or
combines an answer of an opened table; and it was not taken before. -/
theorem PushFits.next {subs : List (A × Option (Nat × Nat))} {reads : List (Nat × Option Nat)}
    {c : Cursor} (h : PushFits subs reads c) {p : Nat × Nat} (hp : c.next = some p) :
    ¬ c.Before p.1 p.2 ∧
      ((∃ x, subs[p.1]? = some (x, none) ∧ reads[p.2]? = some (p.1, none)) ∨
        ∃ x t r, subs[p.1]? = some (x, some t) ∧ reads[p.2]? = some (p.1, some r) ∧ r < t.2) := by
  obtain ⟨⟨r, hr⟩, hn⟩ := (h.2.todo p).1 (Cursor.next_todo hp)
  refine ⟨hn, ?_⟩
  cases r with
  | none =>
    have hlt := h.2.seen _ _ hr
    obtain ⟨e, he⟩ : ∃ e, subs[p.1]? = some e := ⟨subs[p.1], List.getElem?_eq_getElem hlt⟩
    rcases e with ⟨x, _ | t⟩
    · exact .inl ⟨x, he, hr⟩
    · exact absurd ((h.2.isOpen _ _ hr).2 ⟨x, t, he⟩) hn
  | some r =>
    have hlt := h.2.filed _ _ _ hr
    unfold cntOf at hlt
    cases he : subs[p.1]? with
    | none => rw [he] at hlt; cases hlt
    | some e =>
      rcases e with ⟨x, _ | t⟩
      · rw [he] at hlt; cases hlt
      · rw [he] at hlt
        exact .inr ⟨x, t, r, rfl, hr, hlt⟩

theorem Filed.mark_todo {n : Nat} {o : Nat → Prop} {cnt : Nat → Nat}
    {reads : List (Nat × Option Nat)} {c : Cursor} (h : Filed n o cnt reads c) (p : Nat × Nat)
    (t : Nat) (x : Nat × Nat) :
    x ∈ (c.mark p t).todo ↔
      (∃ r : Option Nat, reads[x.2]? = some (x.1, r)) ∧ x ∉ (c.mark p t).done := by
  simp only [Cursor.mark, List.mem_filter, List.mem_cons, bne_iff_ne, ne_eq, not_or]
  rw [h.todo x]
  constructor
  · rintro ⟨⟨hf, hd⟩, hne⟩
    exact ⟨hf, hne, hd⟩
  · rintro ⟨hf, hne, hd⟩
    exact ⟨⟨hf, hd⟩, hne⟩

/-- Marking a unit that combines keeps the fit. -/
theorem PushFits.markRead {subs : List (A × Option (Nat × Nat))}
    {reads : List (Nat × Option Nat)} {c : Cursor} (h : PushFits subs reads c) {p : Nat × Nat}
    {r : Nat} (hr : reads[p.2]? = some (p.1, some r)) (t : Nat) :
    PushFits subs reads (c.mark p t) := by
  refine ⟨h.1, ⟨h.2.pb, h.2.filed, h.2.all, h.2.seen, h.2.opens, h.2.once, fun q s hq => ?_,
    fun x hx => ?_, h.2.mark_todo p t⟩⟩
  · rw [← h.2.isOpen q s hq]
    simp only [Cursor.mark, List.mem_cons]
    constructor
    · rintro (e | e)
      · rw [← e] at hr
        rw [hq] at hr
        simp at hr
      · exact e
    · exact .inr
  · simp only [Cursor.mark, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨_, hr⟩
    · exact h.2.done x hx

theorem cntOf_set_open (subs : List (A × Option (Nat × Nat))) {s : Nat} {x : A}
    (hs : subs[s]? = some (x, none)) (j : Nat) :
    cntOf (subs.set s (x, some (j, 0))) = cntOf subs := by
  funext s'
  unfold cntOf
  by_cases e : s = s'
  · subst e
    rw [List.getElem?_set_self (lt_of_getElem? hs), hs]
  · rw [List.getElem?_set_ne e]

theorem isOpen_set_open (subs : List (A × Option (Nat × Nat))) {s : Nat} {x : A}
    (hs : subs[s]? = some (x, none)) (j : Nat) (s' : Nat) :
    (IsOpen subs s' ∨ s' = s) ↔ IsOpen (subs.set s (x, some (j, 0))) s' := by
  unfold IsOpen
  by_cases e : s = s'
  · subst e
    rw [List.getElem?_set_self (lt_of_getElem? hs)]
    simp
  · rw [List.getElem?_set_ne e]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h.symm e
    · exact .inl

/-- Marking the unit that opens an answer, with the table opened for it,
keeps the fit. -/
theorem PushFits.markOpen {subs : List (A × Option (Nat × Nat))}
    {reads : List (Nat × Option Nat)} {c : Cursor} (h : PushFits subs reads c) {p : Nat × Nat}
    {x : A} (hs : subs[p.1]? = some (x, none)) (hr : reads[p.2]? = some (p.1, none))
    (j t : Nat) :
    PushFits (subs.set p.1 (x, some (j, 0))) reads (c.mark p t) := by
  refine ⟨by rw [List.length_set]; exact h.1, ?_⟩
  rw [List.length_set, cntOf_set_open subs hs j]
  refine Filed.congr (o := fun s => IsOpen subs s ∨ s = p.1) ⟨h.2.pb, h.2.filed, h.2.all,
    h.2.seen, h.2.opens, h.2.once, fun q s hq => ?_, fun y hy => ?_, h.2.mark_todo p t⟩
    (isOpen_set_open subs hs j) rfl
  · simp only [Cursor.mark, List.mem_cons]
    constructor
    · rintro (e | e)
      · exact .inr (congrArg Prod.fst e)
      · exact .inl ((h.2.isOpen q s hq).1 e)
    · rintro (e | e)
      · exact .inr ((h.2.isOpen q s hq).2 e)
      · subst e
        exact .inl (Prod.ext rfl (h.2.once q p.2 p.1 hq hr))
  · simp only [Cursor.mark, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨_, hr⟩
    · exact h.2.done y hy

/-- When no unit is left, every answer seen is opened and every answer filed
is combined. -/
theorem PushFits.done_of_todo {subs : List (A × Option (Nat × Nat))}
    {reads : List (Nat × Option Nat)} {c : Cursor} (h : PushFits subs reads c)
    (ht : c.todo = []) :
    (∀ s, s < subs.length → IsOpen subs s) ∧
      ∀ q s r, reads[q]? = some (s, r) → c.Before s q := by
  have key : ∀ q s r, reads[q]? = some (s, r) → c.Before s q := by
    intro q s r hq
    by_contra hn
    have : (s, q) ∈ c.todo := (h.2.todo (s, q)).2 ⟨⟨r, hq⟩, hn⟩
    rw [ht] at this
    cases this
  refine ⟨fun s hs => ?_, key⟩
  obtain ⟨q, hq⟩ := h.2.opens s hs
  exact (h.2.isOpen q s hq).1 (key q s none hq)

end RwLog.Symmetric
