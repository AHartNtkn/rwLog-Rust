/-
# The fan: a family whose body is dear to read from the wrong end

The member of rank `m` is the program

    h := id ; id ; id ; id ; (g | u ; … ; u) ; c
    c := id | c ; id

with the input `h`. `g` is the ground span `a -> b`, `u` is the union of the
two spans `$x -> (s $x)` and `$x -> (s $x s)`, and there are `m + 2` copies
of `u`. The products of a choice of one span from each copy relate different
pairs, so they are `2 ^ (m + 2)` different relations.

`c` is the identity, and the unfolding race never reads it whole
(`tags`), while `h` relates nothing without it (`hneed`). So the engine
answers for `h` from the tables of its body only. The body is a chain of
six members in either direction, and four of the splits of the chain have a
side that leads, through copies of `id`, into the union that holds the
chain of `u` (`dear`). A reading that composes every whole product at the
edge spends `2 ^ (m + 1)` on such a side, so the first engine has spent as
much before it covers a pair that needs a pair of `h` (`paid`).
-/
import RwLog.Rungs.Symmetric.DearChain
import RwLog.Rungs.Symmetric.RunsCost

namespace RwLog

namespace Symmetric

namespace Fan

open Answer

/-! ## The family -/

/-- `$x -> $x`. -/
def idS : Span := ⟨.var 0, .var 0, []⟩

/-- The identity. -/
def I : Rel := .span idS

/-- One of two ways to wrap a term: `(s t)` and `(s t s)`. -/
def wrap {V : Type} : Bool → Term V → Term V
  | true, t => .app (.sym "s") t
  | false, t => .app (.app (.sym "s") t) (.sym "s")

/-- The span that wraps, the other way round when `last`. -/
def sU : Bool → Bool → Span
  | false, b => ⟨.var 0, wrap b (.var 0), []⟩
  | true, b => ⟨wrap b (.var 0), .var 0, []⟩

/-- The union of the two spans that wrap. -/
def U (last : Bool) : Rel := .or (.span (sU last true)) (.span (sU last false))

/-- The ground span `a -> b`, the other way round when `last`. -/
def gS : Bool → Span
  | false => ⟨.sym "a", .sym "b", []⟩
  | true => ⟨.sym "b", .sym "a", []⟩

/-- The chain of `m + 2` copies of the union. -/
def Bn (m : Nat) (last : Bool) : Rel := mkSeq (List.replicate (m + 2) (U last))

/-- The union of the ground span and the chain. -/
def Ud (m : Nat) (last : Bool) : Rel := .or (.span (gS last)) (Bn m last)

/-- The call of `c`, of its converse when `f`. -/
def cl : Bool → Rel
  | false => .call "c"
  | true => .conv (.call "c")

/-- The members of the body, in the order they are in when the converse is
taken (`last`). -/
def chain (m : Nat) : Bool → Bool → List Rel
  | false, f => [I, I, I, I, Ud m false, cl f]
  | true, f => [cl f, Ud m true, I, I, I, I]

/-- The body of `h`. -/
def body (m : Nat) : Rel := mkSeq (chain m false false)

/-- The body of `c`. -/
def cbody : Rel := .or I (.seq (.call "c") I)

/-- The member of rank `m`. -/
def prog (m : Nat) : Program := ⟨[("h", body m), ("c", cbody)], []⟩

/-! ## The body in normal form, in each direction -/

theorem strict2 {x y : Rel} (h : RelLT x y) (hx : x ≠ .zero) (hy : y ≠ .zero) :
    sortedBranches [x, y] = [x, y] :=
  sortedBranches_of_strict (List.pairwise_pair.2 h) (by simp [hx, hy])

theorem relLT_U (b : Bool) : RelLT (.span (sU b true)) (.span (sU b false)) := by
  cases b <;> decide

theorem nmap_U (b t : Bool) : nmap b t (U false) = U b := by
  have e : nmap b t (U false) =
      mkOr (sortedBranches [.span (sU b true), .span (sU b false)]) := by
    cases b <;> cases t <;> rfl
  rw [e, strict2 (relLT_U b) nofun nofun]
  rfl

theorem normal_U : Normal (U false) := normal_iff_exists.2 ⟨false, U false, (nmap_U false false).symm⟩

theorem notSeq_U (b : Bool) : NotSeq (U b) := nofun

theorem nmap_Bn (m : Nat) (b t : Bool) : nmap b t (Bn m false) = Bn m b := by
  unfold Bn
  rw [nmap_mkSeq b t (by simp) fun x hx => by
    rw [List.eq_of_mem_replicate hx]; exact ⟨normal_U, notSeq_U false⟩]
  have e : (if b then (List.replicate (m + 2) (U false)).reverse
      else List.replicate (m + 2) (U false)) = List.replicate (m + 2) (U false) := by
    cases b <;> simp
  rw [e, List.map_replicate, nmap_U]

theorem bn_isSeq (m : Nat) (b : Bool) : ∃ a c, Bn m b = .seq a c := mkSeq_two (by simp)

theorem nmap_Ud (m : Nat) (b t : Bool) : nmap b t (Ud m false) = Ud m b := by
  have e : nmap b t (Ud m false) = mkOr (sortedBranches
      (orBranches (nmap b t (.span (gS false))) ++ orBranches (nmap b t (Bn m false)))) := by
    cases b <;> cases t <;> rfl
  have eg : nmap b t (.span (gS false)) = .span (gS b) := by cases b <;> cases t <;> rfl
  rw [e, nmap_Bn, eg]
  unfold Ud
  obtain ⟨a, c, hac⟩ := bn_isSeq m b
  rw [hac]
  show mkOr (sortedBranches [.span (gS b), .seq a c]) = _
  rw [strict2 (x := .span (gS b)) (y := .seq a c) ⟨rfl, by simp⟩ (by simp) (by simp)]
  rfl

theorem normal_Ud (m : Nat) : Normal (Ud m false) :=
  normal_iff_exists.2 ⟨false, Ud m false, (nmap_Ud m false false).symm⟩

theorem notSeq_chain (m : Nat) (b f : Bool) : ∀ x ∈ chain m b f, NotSeq x := by
  intro x hx
  cases b <;> cases f <;> simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact nofun

theorem nmap_body (m : Nat) (b t : Bool) : nmap b t (body m) = mkSeq (chain m b (b ^^ t)) := by
  unfold body
  rw [nmap_mkSeq b t (by simp [chain]) fun x hx => ⟨by
    simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · trivial
    · trivial
    · trivial
    · exact normal_Ud m
    · trivial, notSeq_chain m false false x hx⟩]
  have eI : nmap b t I = I := by cases b <;> cases t <;> rfl
  have ec : nmap b t (cl false) = cl (b ^^ t) := by cases b <;> cases t <;> rfl
  cases b <;>
    simp only [chain, Bool.false_eq_true, ite_false, ite_true, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil, eI, ec, nmap_Ud]

/-! ## What the wrappings relate -/

/-- A word of wrappings, the first innermost. -/
def ctx : List Bool → GTerm → GTerm
  | [], t => t
  | b :: w, t => ctx w (wrap b t)

theorem ctx_snoc : ∀ (w : List Bool) (b : Bool) (t : GTerm), ctx (w ++ [b]) t = wrap b (ctx w t)
  | [], _, _ => rfl
  | _ :: w, b, _ => ctx_snoc w b _

theorem wrap_inj {b b' : Bool} {t t' : GTerm} (h : wrap b t = wrap b' t') : b = b' ∧ t = t' := by
  cases b <;> cases b' <;> simp_all [wrap]

theorem ctx_inj : ∀ (w w' : List Bool) (t t' : GTerm), w.length = w'.length →
    ctx w t = ctx w' t' → w = w' ∧ t = t'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | b :: w, b' :: w', t, t', hl, h => by
    obtain ⟨rfl, h'⟩ := ctx_inj w w' _ _ (by simpa using hl) h
    obtain ⟨rfl, rfl⟩ := wrap_inj h'
    exact ⟨rfl, rfl⟩

theorem wrap_bind (b : Bool) (t : Pat) (σ : Nat → GTerm) :
    (wrap b t).bind σ = wrap b (t.bind σ) := by cases b <;> rfl

/-- What a word of wrappings relates, the other way round when `last`. -/
def Wd (last : Bool) (w : List Bool) : PRel :=
  if last then {p | p.1 = ctx w p.2} else {p | p.2 = ctx w p.1}

theorem denAt_sU (M : Interp) (last b : Bool) : (sU last b).denAt M = Wd last [b] := by
  ext p
  cases last
  · simp only [Span.denAt, sU, Wd, ctx, Set.mem_ofPred_eq, List.not_mem_nil, false_imp_iff,
      implies_true, and_true, Bool.false_eq_true, ite_false, wrap_bind, Term.bind_var]
    constructor
    · rintro ⟨σ, h1, h2⟩; rw [h2, h1]
    · intro h; exact ⟨fun _ => p.1, rfl, h⟩
  · simp only [Span.denAt, sU, Wd, ctx, Set.mem_ofPred_eq, List.not_mem_nil, false_imp_iff,
      implies_true, and_true, ite_true, wrap_bind, Term.bind_var]
    constructor
    · rintro ⟨σ, h1, h2⟩; rw [h2, h1]
    · intro h; exact ⟨fun _ => p.2, h, rfl⟩

theorem denAt_idS (M : Interp) : idS.denAt M = {p | p.1 = p.2} := by
  ext p
  simp only [Span.denAt, idS, Set.mem_ofPred_eq, List.not_mem_nil, false_imp_iff, implies_true,
    and_true, Term.bind_var]
  constructor
  · rintro ⟨σ, h1, h2⟩; rw [h2, h1]
  · intro h; exact ⟨fun _ => p.1, rfl, h.symm⟩

theorem wd_snoc (last : Bool) (w : List Bool) (b : Bool) :
    Wd last (w ++ [b]) =
      if last then (Wd last [b]).comp (Wd last w) else (Wd last w).comp (Wd last [b]) := by
  ext p
  cases last
  · simp only [Wd, PRel.comp, ctx_snoc, ctx, Bool.false_eq_true, ite_false, Set.mem_ofPred_eq]
    constructor
    · intro h; exact ⟨_, rfl, h⟩
    · rintro ⟨x, rfl, h⟩; exact h
  · simp only [Wd, PRel.comp, ctx_snoc, ctx, ite_true, Set.mem_ofPred_eq]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨x, h, rfl⟩; exact h

theorem wd_nonempty (last : Bool) (w : List Bool) : (Wd last w).Nonempty := by
  cases last
  · exact ⟨(.sym "", ctx w (.sym "")), rfl⟩
  · exact ⟨(ctx w (.sym ""), .sym ""), rfl⟩

theorem wd_inj (last : Bool) (w w' : List Bool) (hl : w.length = w'.length)
    (h : Wd last w = Wd last w') : w = w' := by
  cases last
  · have : ((.sym "", ctx w (.sym "")) : GTerm × GTerm) ∈ Wd false w' := h ▸ (rfl : _ = _)
    exact (ctx_inj w w' _ _ hl this).1
  · have : ((ctx w (.sym ""), .sym "") : GTerm × GTerm) ∈ Wd true w' := h ▸ (rfl : _ = _)
    exact (ctx_inj w w' _ _ hl this).1

/-! ## A side that is dear to read -/

/-- The members of a side, from the end that is read: `k` copies of `id`,
the union, and the call. -/
def sideL (m : Nat) (last f : Bool) (k : Nat) : List Rel :=
  List.replicate k I ++ [Ud m last, cl f]

/-- A side of the body: a left side when `last`. -/
def side (m : Nat) (last f : Bool) (k : Nat) : Rel :=
  mkSeq (if last then (sideL m last f k).reverse else sideL m last f k)

/-- The sides of the body that are dear to read from the end `last`. -/
def Exp (m : Nat) (n : Rel) (last : Bool) : Prop := ∃ f k, k ≤ 3 ∧ n = side m last f k

section kernel

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
variable {K : Kernel R Cost} {hK : K.Refines D}

omit [DecidableEq R] in
/-- A first-order span that relates a pair has a representative. -/
theorem rep_exists {M : Interp} (hL : D.Lawful M) (s : Span) (hfo : s.firstOrder = true)
    (hne : (s.denAt M).Nonempty) : ∃ r, D.rep s = some r := by
  cases h : D.rep s with
  | some r => exact ⟨r, rfl⟩
  | none =>
    rw [hL.rep_none s hfo h] at hne
    exact absurd hne Set.not_nonempty_empty

/-- **A dear side costs `2 ^ (m + 1)` to read**, at a kernel that charges a
tick or more for a composition, if the reading returns something or is to a
depth of five or more. -/
theorem side_dear {M : Interp} (hL : D.Lawful M) (hc : ∀ a b : R, 1 ≤ (K.compose a b).ticks)
    (m : Nat) (last f : Bool) (k depth : Nat) :
    (5 ≤ depth ∨ ∃ e, (readEdge (K := DerivationKernel.over D K hK P) last depth
        (side m last f k)).val = some e) →
      2 ^ (m + 1) ≤ (readEdge (K := DerivationKernel.over D K hK P) last depth
        (side m last f k)).ticks := by
  obtain ⟨rid, hrid⟩ := rep_exists hL idS rfl (by rw [denAt_idS]; exact ⟨(.sym "", .sym ""), rfl⟩)
  obtain ⟨ra, hra⟩ := rep_exists hL (sU last true) (by cases last <;> rfl)
    (by rw [denAt_sU]; exact wd_nonempty _ _)
  obtain ⟨rb, hrb⟩ := rep_exists hL (sU last false) (by cases last <;> rfl)
    (by rw [denAt_sU]; exact wd_nonempty _ _)
  have hns : ∀ x ∈ sideL m last f k, NotSeq x := by
    intro x hx
    simp only [sideL, List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with ⟨-, rfl⟩ | rfl | rfl
    · exact nofun
    · exact nofun
    · cases f <;> exact nofun
  have hlen : 2 ≤ (sideL m last f k).length := by simp [sideL]
  obtain ⟨a, c, hac⟩ := bn_isSeq m last
  refine readEdge_side_dear (K := K) (hK := hK) (P := P) hL hc last
    (xs := if last then (sideL m last f k).reverse else sideL m last f k)
    (ids := List.replicate k I) (Ud := Ud m last) (tl := [cl f]) (pre := [.span (gS last)])
    (post := []) (B := Bn m last) (bs := List.replicate (m + 2) (U last)) (U := U last)
    (sid := idS) (sa := sU last true) (sb := sU last false) (rid := rid)
    (rsp := fun b => if b then ra else rb) (Wd := Wd last) (m := m)
    ?_ ?_ ?_ hrid ?_ ?_ (by simp) ?_ ?_ (by simp) ?_ ?_ rfl hra hrb ?_ ?_ (wd_nonempty last) ?_ depth
  · exact view_mkSeq (by cases last <;> simpa using hlen) fun x hx =>
      hns x (by cases last <;> simpa using hx)
  · cases last <;> simp [sideL]
  · intro x hx; exact List.eq_of_mem_replicate hx
  · rw [hL.rep_some _ _ hrid, denAt_idS]
    ext p
    simp only [PRel.comp, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, h1, h2⟩; rw [h1, h2]
    · intro h; exact ⟨_, rfl, h⟩
  · intro x hx
    obtain rfl : x = cl f := by simpa using hx
    cases f
    · exact ⟨"c", false, rfl⟩
    · exact ⟨"c", true, rfl⟩
  · unfold Ud
    rw [hac]
    rfl
  · intro x hx
    exact ⟨_, by simpa using hx⟩
  · exact view_mkSeq (by simp) fun x hx => by
      rw [List.eq_of_mem_replicate hx]; exact notSeq_U last
  · cases last <;> simp
  · intro b
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [hL.rep_some _ _ hrb, denAt_sU]
    · simp only [ite_true]
      rw [hL.rep_some _ _ hra, denAt_sU]
  · intro w b _
    rw [wd_snoc]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [hL.rep_some _ _ hrb, denAt_sU]
    · simp only [ite_true]
      rw [hL.rep_some _ _ hra, denAt_sU]
  · intro j w w' h1 h2 e
    exact wd_inj last w w' (h1.trans h2.symm) e

/-- The reading that composes every whole product pays for a dear side. -/
theorem dearRead {M : Interp} (hL : D.Lawful M) (hc : ∀ a b : R, 1 ≤ (K.compose a b).ticks)
    (m : Nat) : DearRead @runsReader K hK P (Exp m) (2 ^ (m + 1)) 5 := by
  rintro last depth n ⟨f, k, -, rfl⟩
  exact side_dear hL hc m last f k depth

/-- A body of `h`, in either direction, is a chain with four dear sides. -/
theorem chain_dear (m : Nat) (b f : Bool) :
    ∃ (xs : List Rel) (Dr : Nat → Bool), (mkSeq (chain m b f)).view = .chain xs ∧
      4 ≤ ((List.range xs.length).drop 1).countP Dr ∧
      ∀ i, Dr i = true → ∃ l r, (mkSeq (chain m b f)).interval 0 i = some l ∧
        (mkSeq (chain m b f)).interval i xs.length = some r ∧ (Exp m l true ∨ Exp m r false) := by
  have hlen : (chain m b f).length = 6 := by cases b <;> rfl
  have hparts : seqParts (mkSeq (chain m b f)) = chain m b f :=
    seqParts_mkSeq (by cases b <;> simp [chain]) (notSeq_chain m b f)
  refine ⟨chain m b f, fun i => if b then decide (2 ≤ i ∧ i ≤ 5) else decide (1 ≤ i ∧ i ≤ 4),
    view_mkSeq (by omega) (notSeq_chain m b f), ?_, fun i hi => ?_⟩
  · rw [hlen]; cases b <;> decide
  · have hi' : 1 ≤ i ∧ i ≤ 5 := by
      cases b
      · have := of_decide_eq_true hi; omega
      · have := of_decide_eq_true hi; omega
    refine ⟨mkSeq (((chain m b f).take i).drop 0),
      mkSeq (((chain m b f).take (chain m b f).length).drop i), ?_, ?_, ?_⟩
    · unfold RelOf.interval RelOf.chainParts
      rw [hparts, ite_of_pos ⟨by omega, by omega⟩]
    · unfold RelOf.interval RelOf.chainParts
      rw [hparts, ite_of_pos ⟨by omega, by omega⟩]
    · cases b
      · have h4 : 1 ≤ i ∧ i ≤ 4 := of_decide_eq_true hi
        obtain ⟨h1, h2⟩ := h4
        refine .inr ⟨f, 4 - i, by omega, ?_⟩
        obtain rfl | rfl | rfl | rfl : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
        all_goals rfl
      · have h4 : 2 ≤ i ∧ i ≤ 5 := of_decide_eq_true hi
        obtain ⟨h1, h2⟩ := h4
        refine .inl ⟨f, i - 2, by omega, ?_⟩
        obtain rfl | rfl | rfl | rfl : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
        all_goals rfl

end kernel

/-! ## The program that is run -/

/-- The recursive branch of the body of `c`, in the mirrored program when
`t`. -/
def xAt : Bool → Rel
  | false => .seq (.call "c") I
  | true => .seq I (.call "c")

/-- The body of `c`, in the mirrored program when `t`. -/
def cbodyAt (t : Bool) : Rel := .or I (xAt t)

theorem nmap_cbody (t : Bool) : nmap t t cbody = cbodyAt t := by
  have e : nmap t t cbody = mkOr (sortedBranches [I, xAt t]) := by cases t <;> rfl
  rw [e, strict2 (x := I) (y := xAt t) (by cases t <;> exact ⟨rfl, by simp [I, xAt]⟩)
    (by simp [I]) (by cases t <;> simp [xAt])]
  rfl

theorem orient_P (P : Program) (q : Rel) :
    (orient P q).P = P.normed ∨ (orient P q).P = P.dual.normed := by
  unfold orient
  split <;> simp [pick_P]

theorem body_h (Kc : Context) (m : Nat) : (Kc.program (prog m)).body "h" = body m := by
  simp [ProgramOf.body, Context.program, prog]

theorem body_c (Kc : Context) (m : Nat) : (Kc.program (prog m)).body "c" = cbody := by
  simp [ProgramOf.body, Context.program, prog, List.lookup_cons]

/-- A program a member is run as, in a context: the member with every body
in normal form, mirrored when `t`. -/
structure IsFan (m : Nat) (Po : Program) (t : Bool) : Prop where
  sorts : Po.sorts = []
  h : Po.body "h" = nmap t t (body m)
  c : Po.body "c" = cbodyAt t

theorem isFan_orient (Kc : Context) (m : Nat) (q : Rel) :
    ∃ t, IsFan m (orient (Kc.program (prog m)) q).P t := by
  rcases orient_P (Kc.program (prog m)) q with e | e
  · refine ⟨false, ?_, ?_, ?_⟩
    · rw [orient_sorts]; rfl
    · rw [e, ProgramOf.normed_body, body_h]; rfl
    · rw [e, ProgramOf.normed_body, body_c, ← nmap_cbody]; rfl
  · refine ⟨true, ?_, ?_, ?_⟩
    · rw [orient_sorts]; rfl
    · rw [e, ProgramOf.normed_body, ProgramOf.dual_body, body_h, nmap_tt]
    · rw [e, ProgramOf.normed_body, ProgramOf.dual_body, body_c, ← nmap_cbody, nmap_tt]

/-- A body of `h` in the program run is the chain, in one of its two
directions. -/
theorem bodyNode_shape {m : Nat} {Po : Program} {t : Bool} (hP : IsFan m Po t) {n : Rel}
    (hn : BodyNode Po "h" n) : ∃ b f, n = mkSeq (chain m b f) := by
  rcases hn with hn | hn
  · have e : n = (Po.body "h").norm := (Option.some.inj hn).symm
    rw [e, hP.h, (normal_nmap t t _).norm_eq, nmap_body]
    exact ⟨_, _, rfl⟩
  · have e : n = (Po.body "h").normConv := (Option.some.inj hn).symm
    have e' : (nmap t t (body m)).normConv = nmap (!t) t (body m) := by
      unfold nmap RelOf.normConv
      rw [normB_normB]
      cases t <;> rfl
    rw [e, hP.h, e', nmap_body]
    exact ⟨_, _, rfl⟩

/-- **The bodies of `h` are dear**: the first engine's reading pays
`2 ^ (m + 1)` for the first round of a goal of either. -/
theorem dear {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {K : Kernel R Cost}
    {hK : K.Refines D} {m : Nat} {Po : Program} {t : Bool} (hP : IsFan m Po t)
    (hL : D.Lawful Po.sorts.interp) (hc : ∀ a b : R, 1 ≤ (K.compose a b).ticks) :
    Dear @runsReader K hK Po (Exp m) (BodyNode Po "h") (2 ^ (m + 1)) :=
  Dear.of_chain (T := 5) (N := 4) (dearRead hL hc m) (by decide) (by decide) fun n hn => by
    obtain ⟨b, f, rfl⟩ := bodyNode_shape hP hn
    exact chain_dear m b f

/-! ## `c` is never read whole, and `h` needs it -/

/-- A ground term for each number. -/
def num : Nat → GTerm
  | 0 => .app (.sym "") (.sym "")
  | j + 1 => .app (.sym "") (num j)

theorem num_inj : ∀ i j, num i = num j → i = j
  | 0, 0, _ => rfl
  | 0, j + 1, h => by cases j <;> simp [num] at h
  | i + 1, 0, h => by cases i <;> simp [num] at h
  | i + 1, j + 1, h => by rw [num_inj i j (by simpa [num] using h)]

theorem num_ne (j : Nat) : num j ≠ .sym "" := by cases j <;> simp [num]

/-- The constraint of the `j`-th tag: a disequality that holds. -/
def tau (j : Nat) : GTerm := .app (.app (.sym neSym) (.sym "")) (num j)

/-- The `j`-th tag: the identity, with its constraint. -/
def xi (j : Nat) : Span := ⟨.var 0, .var 0, [(tau j).toPat]⟩

/-- The identity, with a store. -/
def Diag (S : GStore) : GRel := {x | x.1 = x.2.1 ∧ x.2.2 = S}

theorem xi_den (j : Nat) : (xi j).den = Diag {tau j} := by
  ext ⟨a, b, S⟩
  simp only [Span.den, xi, Store.at, Diag, Set.mem_ofPred_eq, Term.bind_var, List.map_cons,
    List.map_nil, GTerm.toPat_bind, List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
  constructor
  · rintro ⟨σ, h⟩; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; cases h1; cases h2; exact ⟨fun _ => a, rfl⟩

theorem idS_den : idS.den = Diag ∅ := by
  ext ⟨a, b, S⟩
  simp only [Span.den, idS, Store.at, Diag, Set.mem_ofPred_eq, Term.bind_var, List.map_nil,
    List.toFinset_nil]
  constructor
  · rintro ⟨σ, h⟩; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; cases h1; cases h2; exact ⟨fun _ => a, rfl⟩

theorem diag_comp_left (S : GStore) : (Diag S).comp (Diag ∅) = Diag S := by
  ext ⟨a, b, T⟩
  simp only [GRel.comp, Diag, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, S₁, S₂, ⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
    cases h1; cases h2; cases h3; cases h4
    exact ⟨rfl, by simpa using h5⟩
  · rintro ⟨h1, h2⟩
    cases h1; cases h2
    exact ⟨a, _, ∅, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, by simp⟩

theorem diag_comp_right (S : GStore) : (Diag ∅).comp (Diag S) = Diag S := by
  ext ⟨a, b, T⟩
  simp only [GRel.comp, Diag, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, S₁, S₂, ⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
    cases h1; cases h2; cases h3; cases h4
    exact ⟨rfl, by simpa using h5⟩
  · rintro ⟨h1, h2⟩
    cases h1; cases h2
    exact ⟨a, ∅, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, by simp⟩

/-- Every derivation of `c` relates a term only to itself. -/
theorem diag_of_derives {Po : Program} {t : Bool} (hc : Po.body "c" = cbodyAt t) {e : Rel}
    {G : GRel} (h : DerivesG Po e G) :
    (e = .call "c" ∨ e = I ∨ e = cbodyAt t ∨ e = xAt t) → ∀ x ∈ G, x.1 = x.2.1 := by
  induction h with
  | span s =>
    intro hs x hx
    have e : s = idS := by cases t <;> simpa [I, cbodyAt, xAt] using hs
    rw [e, idS_den] at hx
    exact hx.1
  | @orl a b G _ ih =>
    intro hs
    have e : a = I := by cases t <;> simp [I, cbodyAt, xAt] at hs <;> simp [I, hs]
    exact ih (.inr (.inl e))
  | @orr a b G _ ih =>
    intro hs
    have e : b = xAt t := by cases t <;> simp [I, cbodyAt, xAt] at hs <;> simp [xAt, I, hs]
    exact ih (.inr (.inr (.inr e)))
  | @seq a b A B _ _ ih₁ ih₂ =>
    rintro hs x ⟨mid, S₁, S₂, h1, h2, -⟩
    have hab : (a = .call "c" ∨ a = I) ∧ (b = .call "c" ∨ b = I) := by
      cases t <;> simp [I, cbodyAt, xAt] at hs <;> simp [I, hs]
    have e1 := ih₁ (hab.1.elim .inl fun h => .inr (.inl h)) _ h1
    have e2 := ih₂ (hab.2.elim .inl fun h => .inr (.inl h)) _ h2
    exact e1.trans e2
  | and _ _ _ _ => intro hs; cases t <;> simp [I, cbodyAt, xAt] at hs
  | conv _ _ => intro hs; cases t <;> simp [I, cbodyAt, xAt] at hs
  | @call n G _ ih =>
    intro hs
    have e : n = "c" := by cases t <;> simpa [I, cbodyAt, xAt] using hs
    subst e
    rw [hc] at ih
    exact ih (.inr (.inr (.inl rfl)))

/-- **`c` is never read whole**: the tags the unfolding race is fooled by. -/
theorem tags {Po : Program} {t : Bool} (hc : Po.body "c" = cbodyAt t) :
    Unfold.Tags Po "c" xi tau where
  inj := fun i j h => num_inj i j (by simpa [tau] using h)
  tag := fun j x hx => by
    rw [xi_den] at hx
    rw [hx.2]
    simp
  absorb := fun j => by
    show DerivesG _ _ _
    rw [hc]
    refine .orr ?_
    have hcall : DerivesG (Po.withBody "c" (.or (cbodyAt t) (.span (xi j)))) (.call "c")
        (xi j).den := .call (by rw [ProgramOf.withBody_self]; exact .orr (.span _))
    cases t
    · have h := DerivesG.seq hcall (DerivesG.span idS)
      rwa [xi_den, idS_den, diag_comp_left, ← xi_den] at h
    · have h := DerivesG.seq (DerivesG.span idS) hcall
      rwa [xi_den, idS_den, diag_comp_right, ← xi_den] at h
  cover := fun j G hG p ⟨S, hS, _⟩ => by
    have hd := diag_of_derives hc hG (.inl rfl) _ hS
    refine ⟨{tau j}, ?_, ?_⟩
    · rw [xi_den]; exact ⟨hd, rfl⟩
    · intro z hz
      obtain rfl : z = tau j := by simpa using hz
      exact ⟨rfl, (num_ne j).symm⟩

/-- **`h` relates nothing without `c`.** -/
theorem hneed {m : Nat} {Po : Program} {t : Bool} (hh : Po.body "h" = nmap t t (body m)) :
    ∀ s, ¬ Derives (Po.withBody "c" .zero) (Po.body "h") s := by
  have nocall : ∀ s, ¬ Derives (Po.withBody "c" .zero) (.call "c") s := by
    intro s h
    cases h with
    | call h' => rw [ProgramOf.withBody_self] at h'; cases h'
  have inv : ∀ {a b : Rel} {s : Span}, Derives (Po.withBody "c" .zero) (.seq a b) s →
      (∃ s₁, Derives (Po.withBody "c" .zero) a s₁) ∧
        ∃ s₂, Derives (Po.withBody "c" .zero) b s₂ := by
    intro a b s h
    cases h with
    | seq h1 h2 _ => exact ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  intro s h
  rw [hh, nmap_body] at h
  cases t
  · change Derives _ (.seq I (.seq I (.seq I (.seq I (.seq (Ud m false) (.call "c")))))) s at h
    obtain ⟨_, h⟩ := (inv h).2
    obtain ⟨_, h⟩ := (inv h).2
    obtain ⟨_, h⟩ := (inv h).2
    obtain ⟨_, h⟩ := (inv h).2
    obtain ⟨_, h⟩ := (inv h).2
    exact nocall _ h
  · change Derives _ (.seq (.call "c") _) s at h
    obtain ⟨_, h⟩ := (inv h).1
    exact nocall _ h

/-! ## What the first engine pays -/

section run

variable {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))
variable (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)

include hD in
/-- **The first engine has paid `2 ^ (m + 1)` before it covers a pair that
needs a pair of `h`**, in any context, at a kernel that charges a tick or
more for a composition. -/
theorem paid (hc : ∀ S (a b : R S), 1 ≤ ((K S).compose a b).ticks) (m : Nat) (Kc : Context)
    (wf : (Kc.program (prog m)).WellFormed (Kc.query (.call "h")))
    {X : PRel} {y : GTerm × GTerm}
    (hd : Kc.Demands (prog m) (.call "h") (prog m).sorts.interp X y) {n : Nat}
    (hcov : ((engine Unfold.raced @runsReader).costedAt dom K hK).oriented.Covered
      (Kc.program (prog m)) (Kc.query (.call "h")) (prog m).sorts.interp y n) :
    2 ^ (m + 1) ≤ ((engine Unfold.raced @runsReader).costedAt dom K hK).oriented.paid
      (Kc.program (prog m)) (Kc.query (.call "h")) n := by
  obtain ⟨t, hP⟩ := isFan_orient Kc m (Kc.query (.call "h"))
  exact covered_paid_ctx @runsReader dom K hK hD good_runsReader Kc wf (tags hP.c) (hneed hP.h)
    (dear hP (hD _ (wf_orient wf).2.2.1) (hc _)) hd hcov

end run

end Fan

end Symmetric

end RwLog
