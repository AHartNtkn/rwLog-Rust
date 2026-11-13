/-
# From the left, R004 pays for every product of `chain k`

`chain k` is `bit ; (bit ; … ; (bit ; $x -> c))`. R004 answers the unfolding
race of the query by the cheapest of three evaluations, and each of them goes
through the choices of `chain k` one product at a time.

* R002's walk hands on both wrappers at every choice: a chain of wrappers
  always composes, and what stands to the right of a choice is another choice,
  of which the expression says nothing (`walk_chain`).
* R003's shared evaluation reaches `chain j` once for each string of wrappers
  to its left. Different strings leave different interfaces, so the memo never
  answers: an entry is only ever recorded for an interface whose string ends
  in the string being evaluated, and the sibling's string does not
  (`eval_chain`).
* R004's walk from the right starts from the forgetting span, which every
  wrapper can precede, so nothing is pruned and every derivation is visited
  (`walkR_chain`).

A race costs at least what the cheaper of the two costs (`le_race_ticks`), so
R004's first round costs at least `2 ^ k` (`first`), and nothing is emitted
before the end of the first round (`r004_forward`).
-/
import RwLog.Rungs.R005.Family
import RwLog.Rungs.R004.Proofs.Separation.Run

namespace RwLog

namespace R005

namespace Fwd

open Cost R000 R001 R002
open R004 (bit walkR front fits collect pruned)
open R004.Sep (P0 Wrap wrapBy Cont)

/-! ## The query -/

theorem canon_chain : ∀ k, canon (chain k) = chain k
  | 0 => by rw [chain, canon, R004.Sep.canon_bit, canon]
  | k + 1 => by rw [chain, canon, R004.Sep.canon_bit, canon_chain k]

/-- The goal of the query, with no boundaries. -/
abbrev g0 (k : Nat) : Goal := ⟨none, chain k, none⟩

theorem norm_g0 (k : Nat) : (g0 k).norm = (false, g0 k) := by
  rw [GoalOf.norm, canon_chain]
  cases k with
  | zero =>
    rw [chain, GoalOf.stripConv]
    · rfl
    · intro lb a rb h
      cases h
  | succ k =>
    rw [chain, GoalOf.stripConv]
    · rfl
    · intro lb a rb h
      cases h

/-- The state the machine starts from: the table of the query. -/
abbrev st0 (k : Nat) : R001.State := ⟨P0, [⟨g0 k, [], false⟩], false, 0⟩

theorem init_eq (k : Nat) (U : Oracle) :
    (Tabled.machine U).start (sepFam k).1 (sepFam k).2 = st0 k := by
  show R001.StateOf.ofGoal P0 (g0 k) = _
  rw [R001.StateOf.ofGoal, norm_g0]

/-! ## R002's walk -/

theorem staticFirst_chain : ∀ j, staticFirst false (chain j) = none
  | 0 => by simp [chain, bit, staticFirst]
  | j + 1 => by simp [chain, bit, staticFirst]

/-- The walk of a choice goes on to its second wrapper, whatever stands
around it. -/
theorem walk_bit_any (L R : List Span) {K : List Rel → List (List Rel) → Cost Walk}
    (hK : Cont K) (acc : List (List Rel)) :
    (walk P0 0 false bit L R K acc).val.1 = false ∧
      2 ≤ (walk P0 0 false bit L R K acc).ticks := by
  obtain ⟨a1, a2⟩ := R004.Sep.walk_span_any (R004.wrap "0") L R hK acc
  obtain ⟨b1, b2⟩ := R004.Sep.walk_span_any (R004.wrap "1") L R hK
    (walk P0 0 false (.span (R004.wrap "0")) L R K acc).val.2
  rw [bit, walk]
  simp only [bind_val, bind_ticks, tick_ticks, a1, Bool.false_eq_true, ↓reduceIte]
  exact ⟨b1, by omega⟩

/-- The walk of `chain j` after a chain of wrappers does not stop, and goes
through all `2 ^ (j + 1)` products. -/
theorem walk_chain : ∀ (j : Nat) {L : List Span}, (∀ t ∈ L, Wrap t) →
    ∀ {K : List Rel → List (List Rel) → Cost Walk}, Cont K → ∀ acc : List (List Rel),
    (walk P0 0 false (chain j) L [] K acc).val.1 = false ∧
      2 ^ (j + 1) ≤ (walk P0 0 false (chain j) L [] K acc).ticks
  | 0, L, _, K, hK, acc => by
    have h := walk_bit_any L (rightOf false (.span forget) [])
      (K := fun p acc => walk P0 0 false (.span forget) (leftAfter L p) [] (fun q acc => do
        let r ← R002.joinSeq p q
        match r with
        | none => pure (false, acc)
        | some r => do
          let a ← aliveR r []
          if a then K r acc else pure (false, acc)) acc)
      (fun s acc => (R004.Sep.walk_span_any forget _ _ (R004.Sep.cont_join hK s []) acc).1) acc
    rw [chain, walk]
    simp only [bind_val, bind_ticks, tick_ticks]
    refine ⟨h.1, ?_⟩
    have e : 2 ^ (0 + 1) = 2 := rfl
    rw [e]
    exact le_trans h.2 (Nat.le_add_left _ _)
  | j + 1, L, hL, K, hK, acc => by
    have hin : ∀ s, Wrap s → ∀ acc : List (List Rel),
        (walk P0 0 false (chain j) (leftAfter L [.span s]) [] (fun q acc => do
          let r ← R002.joinSeq [.span s] q
          match r with
          | none => pure (false, acc)
          | some r => do
            let a ← aliveR r []
            if a then K r acc else pure (false, acc)) acc).val.1 = false ∧
        2 ^ (j + 1) ≤ (walk P0 0 false (chain j) (leftAfter L [.span s]) [] (fun q acc => do
          let r ← R002.joinSeq [.span s] q
          match r with
          | none => pure (false, acc)
          | some r => do
            let a ← aliveR r []
            if a then K r acc else pure (false, acc)) acc).ticks := by
      intro s hs acc
      have hL' : ∀ t ∈ L ++ [s], Wrap t := by
        intro t ht
        rcases List.mem_append.1 ht with h | h
        · exact hL t h
        · rw [List.mem_singleton.1 h]; exact hs
      exact walk_chain j hL' (R004.Sep.cont_join hK s []) acc
    obtain ⟨h1, h2⟩ := R004.Sep.walk_bit hL (fun p acc =>
      walk P0 0 false (chain j) (leftAfter L p) [] (fun q acc => do
        let r ← R002.joinSeq p q
        match r with
        | none => pure (false, acc)
        | some r => do
          let a ← aliveR r []
          if a then K r acc else pure (false, acc)) acc) hin acc
    rw [chain, walk]
    simp only [rightOf, staticFirst_chain, bind_val, bind_ticks, tick_ticks]
    refine ⟨h1, ?_⟩
    rw [pow_succ, Nat.mul_comm]
    exact le_trans h2 (Nat.le_add_left _ _)

/-- The walk on the query goes through all the products of `chain k`. -/
theorem onDemand_ge (k : Nat) : 2 ^ (k + 1) ≤ (onDemand P0 0 (g0 k)).ticks := by
  have hrel : (g0 k).rel = chain k := rfl
  simp only [onDemand, hrel, bind_ticks]
  exact le_trans (walk_chain k (L := []) (by simp) R004.Sep.cont_top []).2 (Nat.le_add_right _ _)

/-! ## R003's shared evaluation

### What a string of wrappers lets through -/

/-- The terms wrapped by a string, the first symbol outermost. -/
def wset (bs : List Sym) : Set GTerm := {u | ∃ t : GTerm, u = wrapBy bs t}

theorem app_inj {f g : Sym} {a b : GTerm}
    (h : (.app (.sym f) a : GTerm) = .app (.sym g) b) : f = g ∧ a = b := by
  injection h with h1 h2
  injection h1 with h1
  exact ⟨h1, h2⟩

theorem wset_tail {f g : Sym} {bs bs' : List Sym} (h : wset (f :: bs) = wset (g :: bs')) :
    wset bs ⊆ wset bs' := by
  rintro u ⟨t, rfl⟩
  have hm : (.app (.sym f) (wrapBy bs t) : GTerm) ∈ wset (f :: bs) := ⟨t, rfl⟩
  rw [h] at hm
  obtain ⟨t', ht'⟩ := hm
  exact ⟨t', (app_inj ht').2⟩

/-- Different strings let different terms through. -/
theorem wset_inj : ∀ {bs bs' : List Sym}, wset bs = wset bs' → bs = bs'
  | [], [], _ => rfl
  | [], g :: bs', h => by
    have hm : (.sym "" : GTerm) ∈ wset [] := ⟨_, rfl⟩
    rw [h] at hm
    obtain ⟨t, ht⟩ := hm
    cases ht
  | f :: bs, [], h => by
    have hm : (.sym "" : GTerm) ∈ wset [] := ⟨_, rfl⟩
    rw [← h] at hm
    obtain ⟨t, ht⟩ := hm
    cases ht
  | f :: bs, g :: bs', h => by
    have hm : (.app (.sym f) (wrapBy bs (.sym "")) : GTerm) ∈ wset (f :: bs) := ⟨_, rfl⟩
    rw [h] at hm
    obtain ⟨t, ht⟩ := hm
    obtain ⟨rfl, -⟩ := app_inj ht
    rw [wset_inj (Set.Subset.antisymm (wset_tail h) (wset_tail h.symm))]

/-- A wrapper sends the terms wrapped by a string to the terms wrapped by the
longer string. -/
theorem img_wset (f : Sym) (bs : List Sym) : R003.img (wset bs) (R004.wrap f) = wset (f :: bs) := by
  ext u
  constructor
  · rintro ⟨m, ⟨t, rfl⟩, S, hS⟩
    rw [R004.Sep.den_wrap] at hS
    obtain ⟨t', ht'⟩ := hS
    simp only [Prod.mk.injEq] at ht'
    obtain ⟨rfl, rfl, -⟩ := ht'
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨wrapBy bs t, ⟨t, rfl⟩, ∅, ?_⟩
    rw [R004.Sep.den_wrap]
    exact ⟨_, rfl⟩

theorem aliveP_wset (f : Sym) (bs : List Sym) : R003.AliveP (wset bs) (R004.wrap f) := by
  refine ⟨wrapBy bs (.sym ""), ⟨_, rfl⟩, .app (.sym f) (wrapBy bs (.sym "")), ∅, ?_⟩
  rw [R004.Sep.den_wrap]
  exact ⟨_, rfl⟩

/-- The interface lets through exactly the terms wrapped by the string. -/
def Ctx (bs : List Sym) (c : Option Span) : Prop := R003.rng c = wset bs

theorem ctx_nil : Ctx [] none := by
  show (Set.univ : Set GTerm) = wset []
  ext u
  exact ⟨fun _ => ⟨u, rfl⟩, fun _ => trivial⟩

theorem Ctx.alive {bs : List Sym} {c : Option Span} (h : Ctx bs c) (f : Sym) :
    R003.AliveP (R003.rng c) (R004.wrap f) := by
  have h' : R003.rng c = wset bs := h
  rw [h']
  exact aliveP_wset f bs

theorem Ctx.extend {bs : List Sym} {c : Option Span} (h : Ctx bs c) (f : Sym) :
    Ctx (f :: bs) (R003.extend c (R004.wrap f)).val := by
  have h' : R003.rng c = wset bs := h
  show R003.rng _ = wset (f :: bs)
  rw [R003.rng_extend (h.alive f), h', img_wset]

theorem Ctx.inj {bs bs' : List Sym} {c : Option Span} (h : Ctx bs c) (h' : Ctx bs' c) :
    bs = bs' := wset_inj (Eq.trans (Eq.symm h) h')

/-! ### What the memo holds -/

/-- No entry of the memo is for an interface whose string ends in `bs`. -/
def Free (bs : List Sym) (m : R003.Memo) : Prop :=
  ∀ p ∈ m, ∀ bs', Ctx bs' p.1.ctx → ¬ bs <:+ bs'

/-- Every entry of `m'` that is not in `m` is for an interface whose string
ends in `bs`. -/
def Under (bs : List Sym) (m m' : R003.Memo) : Prop :=
  ∀ p ∈ m', p ∈ m ∨ ∃ bs', Ctx bs' p.1.ctx ∧ bs <:+ bs'

/-- The memo has no answer for an interface it holds no entry for. -/
theorem lookup_none {bs : List Sym} {m : R003.Memo} {k : R003.Key} (hf : Free bs m)
    (hc : Ctx bs k.ctx) : (R003.lookup m k).val = none := by
  cases h : (R003.lookup m k).val with
  | none => rfl
  | some s =>
    simp only [R003.lookup, bind_val, pure_val, findL_val, Option.map_eq_some_iff] at h
    obtain ⟨⟨k', s'⟩, hfind, -⟩ := h
    have hk : (R003.sameKey k' k).val = true := by
      have := List.find?_some hfind
      exact this
    have hr := (R003.sameKey_spec hk).2.2.2
    exact absurd (List.suffix_refl bs)
      (hf _ (List.mem_of_find?_eq_some hfind) bs (Eq.trans hr hc))

/-- Without an answer in the memo, the body is run and its summary recorded. -/
theorem memo_miss {k : R003.Key} {m : R003.Memo}
    {body : R003.Memo → Cost (R003.Summary × R003.Memo)} (h : (R003.lookup m k).val = none) :
    (R003.memo k m body).val.2 = (k, (body m).val.1) :: (body m).val.2 ∧
      (body m).ticks ≤ (R003.memo k m body).ticks := by
  simp only [R003.memo, bind_val, bind_ticks, h]
  exact ⟨rfl, Nat.le_add_left _ _⟩

theorem eval_span_memo (s : Span) (c : Option Span) (m : R003.Memo) :
    (R003.eval P0 0 false (.span s) c m).val.2 = m := by
  rw [R003.eval]
  rfl

/-- The evaluation of a choice records at most an entry for its own
interface. -/
theorem eval_bit_memo (c : Option Span) (m : R003.Memo) :
    ∀ p ∈ (R003.eval P0 0 false bit c m).val.2, p ∈ m ∨ p.1.ctx = c := by
  intro p hp
  rw [bit, R003.eval] at hp
  simp only [R003.memo, bind_val] at hp
  cases hl : (R003.lookup m ⟨false, .or (.span (R004.wrap "0")) (.span (R004.wrap "1")), 0, c⟩).val with
  | some s =>
    rw [hl] at hp
    exact Or.inl hp
  | none =>
    rw [hl] at hp
    simp only [bind_val, pure_val, eval_span_memo, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Or.inr rfl
    · exact Or.inl hp

/-- After the interface of a string, a choice has its two wrappers and
nothing else. -/
theorem eval_bit {bs : List Sym} {c : Option Span} {m : R003.Memo} (hc : Ctx bs c)
    (hm : R003.MemoOK P0 m) :
    (R003.eval P0 0 false bit c m).val.1.spans = [R004.wrap "0", R004.wrap "1"] ∧
      (R003.eval P0 0 false bit c m).val.1.opens = [] ∧
      R003.MemoOK P0 (R003.eval P0 0 false bit c m).val.2 := by
  obtain ⟨⟨hs, ho⟩, hm'⟩ := (R003.eval_ok P0 0 bit false) c m hm
  have hN : R000.norm false (R000.unfoldN P0 0 bit) =
      [R004.wrap "0", R004.wrap "1"].map fun s => [RelOf.span s] := rfl
  have hf : [R004.wrap "0", R004.wrap "1"].filter (R003.aliveB (R003.rng c)) = [R004.wrap "0", R004.wrap "1"] := by
    refine List.filter_eq_self.2 fun s hs => R003.aliveB_iff.2 ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact hc.alive _
    · exact hc.alive _
  have hd : [R004.wrap "0", R004.wrap "1"].eraseDups = [R004.wrap "0", R004.wrap "1"] := by decide
  have hO : R003.OpenR (R000.norm false (R000.unfoldN P0 0 bit)) (R003.rng c) = ∅ := by
    rw [hN, Set.eq_empty_iff_forall_notMem]
    rintro t ⟨p, hp, hsp, -, -⟩
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hp
    cases hsp
  refine ⟨?_, R003.ranges_eq_empty.1 (ho.trans hO), hm'⟩
  rw [hs, hN, R004.Sep.closed_map, hf, firsts_eq_eraseDups, hd]

/-! ### A sequence that starts with a choice -/

theorem afterSpan_second (c : Option Span)
    (second : Option Span → R003.Memo → Cost (R003.Summary × R003.Memo)) (acc : R003.Acc)
    (x : Span) :
    (R003.afterSpan c second acc x).val.2.2 = (second (R003.extend c x).val acc.2.2).val.2 ∧
      (second (R003.extend c x).val acc.2.2).ticks ≤ (R003.afterSpan c second acc x).ticks := by
  simp only [R003.afterSpan, bind_val, bind_ticks, pure_val]
  exact ⟨trivial, by omega⟩

theorem seqSummary_two {c : Option Span} {first : R003.Summary}
    {second : Option Span → R003.Memo → Cost (R003.Summary × R003.Memo)} {m : R003.Memo}
    {a b : Span} (hs : first.spans = [a, b]) (ho : first.opens = []) :
    (R003.seqSummary c first second m).val.2 =
        (R003.afterSpan c second (R003.afterSpan c second ([], [], m) a).val b).val.2.2 ∧
      (R003.afterSpan c second ([], [], m) a).ticks +
          (R003.afterSpan c second (R003.afterSpan c second ([], [], m) a).val b).ticks ≤
        (R003.seqSummary c first second m).ticks := by
  simp only [R003.seqSummary, hs, ho, foldL, bind_val, bind_ticks, pure_val, pure_ticks]
  exact ⟨trivial, by omega⟩

theorem not_suffix_cons (f : Sym) (bs : List Sym) : ¬ (f :: bs) <:+ bs := by
  intro h
  have := h.length_le
  simp only [List.length_cons] at this
  omega

theorem not_suffix_both {bs bs' : List Sym} (h0 : ("0" :: bs) <:+ bs')
    (h1 : ("1" :: bs) <:+ bs') : False := by
  have e := (List.suffix_of_suffix_length_le h0 h1 (by simp)).eq_of_length (by simp)
  injection e with e
  exact absurd e (by decide)

/-- If the second factor costs at least `n` after every interface the memo
holds no entry for, and only records entries under that interface, then the
sequence of a choice and it costs twice that, and likewise only records
entries under its own interface. -/
theorem seq_step (B : Rel) (n : Nat)
    (hB : ∀ (bs : List Sym) (c : Option Span) (m : R003.Memo), Ctx bs c → R003.MemoOK P0 m →
      Free bs m → n ≤ (R003.eval P0 0 false B c m).ticks ∧
        Under bs m (R003.eval P0 0 false B c m).val.2)
    {bs : List Sym} {c : Option Span} {m : R003.Memo} (hc : Ctx bs c) (hm : R003.MemoOK P0 m)
    (hf : Free bs m) :
    2 * n + 1 ≤ (R003.eval P0 0 false (.seq bit B) c m).ticks ∧
      Under bs m (R003.eval P0 0 false (.seq bit B) c m).val.2 := by
  obtain ⟨hsp, hop, hm1⟩ := eval_bit hc hm
  have hmem1 := eval_bit_memo c m
  -- the memo after the choice holds no entry under either longer string
  have hfree : ∀ f : Sym, Free (f :: bs) (R003.eval P0 0 false bit c m).val.2 := by
    intro f p hp bs' hc' hsuf
    rcases hmem1 p hp with hin | hctx
    · exact hf p hin bs' hc' ((List.suffix_cons f bs).trans hsuf)
    · rw [hctx] at hc'
      rw [hc'.inj hc] at hsuf
      exact not_suffix_cons f bs hsuf
  -- after the first wrapper
  obtain ⟨t0, u0⟩ := hB _ _ _ (hc.extend "0") hm1 (hfree "0")
  have hm2 := ((R003.eval_ok P0 0 B false) (R003.extend c (R004.wrap "0")).val _ hm1).2
  dsimp only at hm2
  -- after the second: what the first recorded is under the other string
  have hf1 : Free ("1" :: bs) (R003.eval P0 0 false B (R003.extend c (R004.wrap "0")).val
      (R003.eval P0 0 false bit c m).val.2).val.2 := by
    intro p hp bs' hc' hsuf
    rcases u0 p hp with hin | ⟨bs'', hc'', hsuf''⟩
    · exact hfree "1" p hin bs' hc' hsuf
    · rw [hc'.inj hc''] at hsuf
      exact not_suffix_both hsuf'' hsuf
  obtain ⟨t1, u1⟩ := hB _ _ _ (hc.extend "1") hm2 hf1
  have hl := lookup_none (k := ⟨false, .seq bit B, 0, c⟩) hf hc
  obtain ⟨sv, st⟩ := seqSummary_two (c := c)
    (second := fun c m => R003.eval P0 0 false B c m)
    (m := (R003.eval P0 0 false bit c m).val.2) hsp hop
  obtain ⟨av, at_⟩ := afterSpan_second c (fun c m => R003.eval P0 0 false B c m)
    ([], [], (R003.eval P0 0 false bit c m).val.2) (R004.wrap "0")
  obtain ⟨bv, bt⟩ := afterSpan_second c (fun c m => R003.eval P0 0 false B c m)
    (R003.afterSpan c (fun c m => R003.eval P0 0 false B c m)
      ([], [], (R003.eval P0 0 false bit c m).val.2) (R004.wrap "0")).val (R004.wrap "1")
  dsimp only at av at_ bv bt
  rw [av] at bv bt
  rw [bv] at sv
  rw [R003.eval]
  refine ⟨le_trans ?_ (memo_miss hl).2, ?_⟩
  · simp only [bind_ticks, tick_ticks]
    omega
  · rw [(memo_miss hl).1]
    simp only [bind_val]
    rw [sv]
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact Or.inr ⟨bs, hc, List.suffix_refl bs⟩
    · rcases u1 p hp with hp | ⟨bs', hc', hsuf⟩
      · rcases u0 p hp with hp | ⟨bs', hc', hsuf⟩
        · rcases hmem1 p hp with hp | hctx
          · exact Or.inl hp
          · exact Or.inr ⟨bs, by rw [hctx]; exact hc, List.suffix_refl bs⟩
        · exact Or.inr ⟨bs', hc', (List.suffix_cons _ bs).trans hsuf⟩
      · exact Or.inr ⟨bs', hc', (List.suffix_cons _ bs).trans hsuf⟩

/-- The shared evaluation of `chain j` after the interface of a string the
memo holds nothing under costs at least `2 ^ j`. -/
theorem eval_chain : ∀ (j : Nat) (bs : List Sym) (c : Option Span) (m : R003.Memo), Ctx bs c →
    R003.MemoOK P0 m → Free bs m → 2 ^ j ≤ (R003.eval P0 0 false (chain j) c m).ticks ∧
      Under bs m (R003.eval P0 0 false (chain j) c m).val.2
  | 0, bs, c, m, hc, hm, hf => by
    have h := seq_step (.span forget) 0 (fun bs c m _ _ _ =>
      ⟨Nat.zero_le _, fun p hp => Or.inl (by rwa [eval_span_memo] at hp)⟩) hc hm hf
    rw [chain]
    exact ⟨h.1, h.2⟩
  | j + 1, bs, c, m, hc, hm, hf => by
    have h := seq_step (chain j) (2 ^ j) (eval_chain j) hc hm hf
    rw [chain]
    refine ⟨?_, h.2⟩
    rw [pow_succ]
    exact le_trans (by omega) h.1

/-- The shared evaluation of the query reaches the forgetting span once for
each string of wrappers. -/
theorem shared_ge (k : Nat) : 2 ^ k ≤ (R003.shared P0 0 (g0 k)).ticks := by
  have hrel : (g0 k).rel = chain k := rfl
  simp only [R003.shared, hrel, bind_ticks]
  exact le_trans (eval_chain k [] none [] ctx_nil (R003.memoOK_nil P0)
    (fun p hp => by cases hp)).1 (Nat.le_add_right _ _)

/-! ## R004's walk from the right -/

/-- A derivation of `chain j`: a string of wrappers and the forgetting
span. -/
def pth : List Span → Rel
  | [] => .span forget
  | s :: L => .seq (.span s) (pth L)

theorem front_pth : ∀ L : List Span, front (pth L) [] = L ++ [forget]
  | [] => rfl
  | s :: L => by simp [pth, front, front_pth L]

theorem den_forget (t : GTerm) : (t, .sym "c", (∅ : GStore)) ∈ forget.den :=
  ⟨fun _ => t, by simp [forget, Store.at]⟩

/-- A chain of wrappers followed by the forgetting span relates every term to
`c`. -/
theorem chain_pth_total : ∀ L : List Span, (∀ s ∈ L, Wrap s) → ∀ t : GTerm,
    (t, .sym "c", (∅ : GStore)) ∈ GRel.chain ((L ++ [forget]).map Span.den)
  | [], _, t => ⟨.sym "c", ∅, ∅, den_forget t, ⟨rfl, rfl⟩, by simp⟩
  | s :: L, h, t => by
    have hs : ∃ f, s = R004.wrap f := by
      rcases h s (by simp) with rfl | rfl
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    obtain ⟨f, rfl⟩ := hs
    have hu := chain_pth_total L (fun x hx => h x (by simp [hx])) (.app (.sym f) t)
    refine ⟨.app (.sym f) t, ∅, ∅, ?_, hu, by simp⟩
    rw [R004.Sep.den_wrap]
    exact ⟨t, rfl⟩

/-- Every wrapper can precede a derivation, so the walk from the right prunes
nothing. -/
theorem fits_pth {s : Span} (hs : Wrap s) {L : List Span} (hL : ∀ t ∈ L, Wrap t) :
    (fits s (L ++ [forget])).val = true := by
  have hc : (Span.chain (s :: (L ++ [forget]))).isSome = true := by
    rw [Span.chain_isSome_iff]
    refine ⟨_, chain_pth_total (s :: L) (fun t ht => ?_) (.sym "")⟩
    rcases List.mem_cons.1 ht with rfl | ht
    · exact hs
    · exact hL t ht
  cases L with
  | nil => simpa [fits, Charged.composable] using hc
  | cons a L => simpa [fits, Charged.composable] using hc

/-- The walk from the right of a span that fits hands it on. -/
theorem walkR_span {α : Type} (s : Span) {R : List Span} (hfit : (fits s R).val = true)
    (K : R004.Path → α → Cost (Bool × α)) (acc : α) :
    (walkR P0 0 false (.span s) R K acc).val.1 = (K ⟨.leaf, .span s⟩ acc).val.1 ∧
      (K ⟨.leaf, .span s⟩ acc).ticks + 1 ≤ (walkR P0 0 false (.span s) R K acc).ticks := by
  rw [walkR]
  simp only [Bool.false_eq_true, ↓reduceIte, bind_val, bind_ticks, tick_ticks, hfit]
  exact ⟨trivial, by omega⟩

/-- The walk from the right of a choice whose wrappers both fit hands both
on. -/
theorem walkR_bit {α : Type} {R : List Span} (hfit : ∀ s, Wrap s → (fits s R).val = true)
    {K : R004.Path → α → Cost (Bool × α)} {c : Nat}
    (hK : ∀ key s, Wrap s → ∀ acc,
      (K ⟨key, .span s⟩ acc).val.1 = false ∧ c ≤ (K ⟨key, .span s⟩ acc).ticks) (acc : α) :
    (walkR P0 0 false bit R K acc).val.1 = false ∧
      2 * (c + 1) ≤ (walkR P0 0 false bit R K acc).ticks := by
  obtain ⟨a1, a2⟩ := walkR_span (R004.wrap "0") (hfit _ (Or.inl rfl))
    (fun x acc => K ⟨.inl x.key, x.pe⟩ acc) acc
  obtain ⟨c1, c2⟩ := hK (.inl .leaf) (R004.wrap "0") (Or.inl rfl) acc
  have h1 : (walkR P0 0 false (.span (R004.wrap "0")) R
      (fun x acc => K ⟨.inl x.key, x.pe⟩ acc) acc).val.1 = false := a1.trans c1
  have t1 : c + 1 ≤ (walkR P0 0 false (.span (R004.wrap "0")) R
      (fun x acc => K ⟨.inl x.key, x.pe⟩ acc) acc).ticks :=
    le_trans (Nat.add_le_add_right c2 1) a2
  obtain ⟨b1, b2⟩ := walkR_span (R004.wrap "1") (hfit _ (Or.inr rfl))
    (fun y acc => K ⟨.inr y.key, y.pe⟩ acc)
    (walkR P0 0 false (.span (R004.wrap "0")) R (fun x acc => K ⟨.inl x.key, x.pe⟩ acc) acc).val.2
  obtain ⟨d1, d2⟩ := hK (.inr .leaf) (R004.wrap "1") (Or.inr rfl)
    (walkR P0 0 false (.span (R004.wrap "0")) R (fun x acc => K ⟨.inl x.key, x.pe⟩ acc) acc).val.2
  have h2 := b1.trans d1
  have t2 := le_trans (Nat.add_le_add_right d2 1) b2
  rw [bit, walkR]
  simp only [bind_val, bind_ticks, tick_ticks, h1, Bool.false_eq_true, ↓reduceIte]
  exact ⟨h2, by omega⟩

/-- The walk from the right of `chain j` does not stop, and hands on all
`2 ^ (j + 1)` derivations. -/
theorem walkR_chain {α : Type} : ∀ (j : Nat) (K : R004.Path → α → Cost (Bool × α)) (c : Nat),
    (∀ key L, (∀ t ∈ L, Wrap t) → ∀ acc,
      (K ⟨key, pth L⟩ acc).val.1 = false ∧ c ≤ (K ⟨key, pth L⟩ acc).ticks) →
    ∀ acc : α, (walkR P0 0 false (chain j) [] K acc).val.1 = false ∧
      2 ^ (j + 1) * (c + 1) ≤ (walkR P0 0 false (chain j) [] K acc).ticks
  | 0, K, c, hK, acc => by
    have hb := walkR_bit (R := [forget]) (fun s hs => fits_pth hs (L := []) (by simp))
      (K := fun p acc => K ⟨.pair p.key .leaf, .seq p.pe (.span forget)⟩ acc) (c := c)
      (fun key s hs acc => hK (.pair key .leaf) [s]
        (fun t ht => by rw [List.mem_singleton.1 ht]; exact hs) acc) acc
    obtain ⟨a1, a2⟩ := walkR_span forget (R := []) rfl
      (fun q acc => walkR P0 0 false bit (front q.pe [])
        (fun p acc => K ⟨.pair p.key q.key, .seq p.pe q.pe⟩ acc) acc) acc
    rw [chain, walkR]
    simp only [bind_val, bind_ticks, tick_ticks]
    refine ⟨a1.trans hb.1, ?_⟩
    have e : 2 ^ (0 + 1) * (c + 1) = 2 * (c + 1) := by rw [Nat.zero_add, pow_one]
    rw [e]
    exact le_trans hb.2 (le_trans (Nat.le_add_right _ 1) (le_trans a2 (Nat.le_add_left _ _)))
  | j + 1, K, c, hK, acc => by
    have ih := walkR_chain j
      (fun q acc => walkR P0 0 false bit (front q.pe [])
        (fun p acc => K ⟨.pair p.key q.key, .seq p.pe q.pe⟩ acc) acc) (2 * (c + 1))
      (fun key L hL acc => by
        have h := walkR_bit (R := L ++ [forget]) (fun s hs => fits_pth hs hL)
          (K := fun p acc => K ⟨.pair p.key key, .seq p.pe (pth L)⟩ acc) (c := c)
          (fun key' s hs acc => hK (.pair key' key) (s :: L) (fun t ht => by
            rcases List.mem_cons.1 ht with rfl | ht
            · exact hs
            · exact hL t ht) acc) acc
        rw [← front_pth L] at h
        exact h) acc
    rw [chain, walkR]
    simp only [bind_val, bind_ticks, tick_ticks]
    refine ⟨ih.1, ?_⟩
    have e : 2 ^ (j + 1 + 1) * (c + 1) = 2 ^ (j + 1) * (2 * (c + 1)) := by
      rw [pow_succ, Nat.mul_assoc]
    rw [e]
    exact le_trans (Nat.mul_le_mul_left _ (Nat.le_succ _)) (le_trans ih.2 (Nat.le_add_left _ _))

/-- The product of a derivation is a single span or nothing. -/
theorem norm_pth : ∀ L : List Span, ∀ p ∈ norm false (pth L), ∃ s, p = [RelOf.span s]
  | [], p, hp => by
    have e : norm false (pth []) = [[RelOf.span forget]] := rfl
    rw [e, List.mem_singleton] at hp
    exact ⟨forget, hp⟩
  | s :: L, p, hp => by
    rw [pth, norm] at hp
    simp only [norm, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_filterMap] at hp
    obtain ⟨q, hq, hj⟩ := hp
    obtain ⟨t, rfl⟩ := norm_pth L q hq
    cases hc : s.compose t with
    | none => simp [R000.joinSeq, hc] at hj
    | some z =>
      simp [R000.joinSeq, hc] at hj
      exact ⟨z, hj.symm⟩

/-- `collect` does not stop on a derivation: there is no call in it. -/
theorem collect_pth (key : R004.Key) (L : List Span) (acc : List R004.Found) :
    (collect ⟨key, pth L⟩ acc).val.1 = false := by
  have h : R004.closedP ⟨key, pth L⟩ = true := by
    rw [R004.closedP, List.all_eq_true]
    intro p hp
    obtain ⟨s, rfl⟩ := norm_pth L p hp
    rfl
  rw [R004.collect_val, h]
  rfl

/-- The evaluation pruned from the right visits every derivation of
`chain k`. -/
theorem pruned_ge (k : Nat) : 2 ^ (k + 1) ≤ (pruned P0 0 (g0 k)).ticks := by
  have hrel : (g0 k).rel = chain k := rfl
  have h := (walkR_chain k collect 0
    (fun key L _ acc => ⟨collect_pth key L acc, Nat.zero_le _⟩) []).2
  rw [Nat.zero_add, Nat.mul_one] at h
  simp only [pruned, hrel, bind_ticks]
  exact le_trans h (Nat.le_add_right _ _)

/-! ## The round -/

/-- R004's unfolding race on the query costs at least `2 ^ k`. -/
theorem unfolder_ge (k : Nat) : 2 ^ k ≤ (R004.unfolder P0 0 (g0 k)).ticks := by
  have hp : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ k)
  have h3 : 2 ^ k ≤ (R003.unfolder P0 0 (g0 k)).ticks :=
    le_trans (le_min (le_trans hp (onDemand_ge k)) (shared_ge k)) (Cost.le_race_ticks _ _)
  exact le_trans (le_min h3 (le_trans hp (pruned_ge k))) (Cost.le_race_ticks _ _)

/-- R004's first round costs at least its unfolding race on the query. -/
theorem first (k : Nat) : 2 ^ k ≤ (R004.costed.step (st0 k)).ticks := by
  obtain ⟨K, hK⟩ := Tabled.round_split (st0 k)
  have s1 := (R003.Sep.step_emit (U := R004.unfolder) (st := st0 k) rfl).2
  have e : (R004.costed.step (st0 k)).ticks = _ := s1
  have h := unfolder_ge k
  rw [e, hK R004.unfolder]
  simp only [bind_ticks, tick_ticks, mapL, Tabled.ask, Bool.false_eq_true, ↓reduceIte, pure_ticks]
  omega

end Fwd

/-- From the left: R004 has paid at least `2 ^ k` at any step at which it has
covered anything on `chain k`. -/
theorem r004_forward : Obligation.r004_forward := by
  rintro k n M x ⟨a, ha, -⟩
  have hi : R004.costed.start (sepFam k).1 (sepFam k).2 = Fwd.st0 k :=
    Fwd.init_eq k R004.unfolder
  have hp : R004.costed.paid (sepFam k).1 (sepFam k).2 n = (sepFam k).2.size +
      R004.costed.spent (R004.costed.start (sepFam k).1 (sepFam k).2) n :=
    Tabled.paid_eq R004.unfolder _ _ n
  rw [hp]
  rw [hi] at ha ⊢
  exact le_trans (R004.costed.le_spent_of_covered (N := 0) rfl
    (le_trans (Fwd.first k) (R003.Sep.spent_ge_step _ _ 0)) ha) (Nat.le_add_left _ _)

end R005

end RwLog
