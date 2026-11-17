/-
# The diving engine on the fan

The first reading of the diving engine, by the number 0, takes the first
member of every union. On a member of the fan (`Symmetric/Fan.lean`), in
either direction, the first member of the union in the body of `h` is the
ground span and the first member of the body of `c` is the identity. So the
first reading makes an answer of `h` from five copies of the identity and
the ground span, and never reads the chain of unions: to a depth of five it
costs the same whatever the rank (`reads_root`, at most `fanTicks`).
-/
import RwLog.Rungs.Dive.Read
import RwLog.Rungs.Symmetric.Fan

open RwLog.Symmetric RwLog.Symmetric.Fan

namespace RwLog

namespace Dive

open Answer

/-! ## The nodes of a member -/

/-- The body of `c`, in each direction of each program: the union of the
identity and a chain. -/
theorem cbody_or (b t : Bool) : ∃ p q, nmap b t cbody = .or I (.seq p q) := by
  cases b <;> cases t
  · refine ⟨.call "c", I, ?_⟩
    rw [show nmap false false cbody = mkOr (sortedBranches [I, .seq (.call "c") I]) from rfl,
      strict2 ⟨rfl, by simp [I]⟩ (by simp [I]) (by simp)]
    rfl
  · refine ⟨.conv (.call "c"), I, ?_⟩
    rw [show nmap false true cbody = mkOr (sortedBranches [I, .seq (.conv (.call "c")) I]) from rfl,
      strict2 ⟨rfl, by simp [I]⟩ (by simp [I]) (by simp)]
    rfl
  · refine ⟨I, .conv (.call "c"), ?_⟩
    rw [show nmap true false cbody = mkOr (sortedBranches [I, .seq I (.conv (.call "c"))]) from rfl,
      strict2 ⟨rfl, by simp [I]⟩ (by simp [I]) (by simp)]
    rfl
  · refine ⟨I, .call "c", ?_⟩
    rw [show nmap true true cbody = mkOr (sortedBranches [I, .seq I (.call "c")]) from rfl,
      strict2 ⟨rfl, by simp [I]⟩ (by simp [I]) (by simp)]
    rfl

theorem normConv_nmap (t : Bool) (e : Rel) : (nmap t t e).normConv = nmap (!t) t e := by
  unfold nmap RelOf.normConv
  rw [normB_normB]
  cases t <;> rfl

/-- The call of `h`, of its converse when `c`. -/
def hl : Bool → Rel
  | false => .call "h"
  | true => .conv (.call "h")

variable {m : Nat} {Po : Program} {t : Bool}

/-- The body a call of `c` reads is the union of the identity and a
chain. -/
theorem body_cl (hP : IsFan m Po t) (f : Bool) :
    ∃ p q, Charged.bodyOf Po (cl f) = some (.or I (.seq p q)) := by
  cases f
  · obtain ⟨p, q, e⟩ := cbody_or t t
    refine ⟨p, q, ?_⟩
    show some (Po.body "c").norm = _
    rw [hP.c, ← nmap_cbody, (normal_nmap t t _).norm_eq, e]
  · obtain ⟨p, q, e⟩ := cbody_or (!t) t
    refine ⟨p, q, ?_⟩
    show some (Po.body "c").normConv = _
    rw [hP.c, ← nmap_cbody, normConv_nmap, e]

/-- The body a call of `h` reads is the chain, forwards or backwards. -/
theorem body_hl (hP : IsFan m Po t) (c : Bool) :
    Charged.bodyOf Po (hl c) = some (mkSeq (chain m (c ^^ t) c)) := by
  cases c
  · show some (Po.body "h").norm = _
    rw [hP.h, (normal_nmap t t _).norm_eq, nmap_body]
    cases t <;> rfl
  · show some (Po.body "h").normConv = _
    rw [hP.h, normConv_nmap, nmap_body]
    cases t <;> rfl

/-! ## The representatives of a member -/

theorem comp_id_left (X : PRel) : PRel.comp {p | p.1 = p.2} X = X := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨z, hz, h⟩
    have e : x = z := hz
    subst e
    exact h
  · intro h
    exact ⟨x, rfl, h⟩

theorem comp_id_right (X : PRel) : PRel.comp X {p | p.1 = p.2} = X := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨z, h, hz⟩
    have e : z = y := hz
    subst e
    exact h
  · intro h
    exact ⟨y, h, rfl⟩

section

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {M : Interp}

omit [DecidableEq R] in
/-- The representative of the identity composes onto another from the left
and leaves it as it is. -/
theorem compose_id_left (hL : D.Lawful M) {i : R} (hi : den M i = {p | p.1 = p.2}) (x : R) :
    D.compose i x = some x := by
  cases h : D.compose i x with
  | none =>
    have e := hL.compose_none i x h
    rw [hi, comp_id_left] at e
    exact absurd (e ▸ hL.live x) Set.not_nonempty_empty
  | some c =>
    have e := hL.compose_some i x c h
    rw [hi, comp_id_left] at e
    rw [hL.canon c x e]

omit [DecidableEq R] in
theorem compose_id_right (hL : D.Lawful M) {i : R} (hi : den M i = {p | p.1 = p.2}) (x : R) :
    D.compose x i = some x := by
  cases h : D.compose x i with
  | none =>
    have e := hL.compose_none x i h
    rw [hi, comp_id_right] at e
    exact absurd (e ▸ hL.live x) Set.not_nonempty_empty
  | some c =>
    have e := hL.compose_some x i c h
    rw [hi, comp_id_right] at e
    rw [hL.canon c x e]

omit [DecidableEq R] in
/-- The identity has a representative, and it relates a term to itself. -/
theorem rep_I (hL : D.Lawful M) : ∃ i, D.rep idS = some i ∧ den M i = {p | p.1 = p.2} := by
  obtain ⟨i, hi⟩ := rep_exists hL idS rfl
    ⟨(.sym "a", .sym "a"), by rw [denAt_idS]; rfl⟩
  exact ⟨i, hi, by rw [hL.rep_some idS i hi, denAt_idS]⟩

/-- The target, the other way round when `b`. -/
def way : Bool → GTerm × GTerm
  | false => (.sym "a", .sym "b")
  | true => (.sym "b", .sym "a")

theorem mem_gS (b : Bool) : way b ∈ (gS b).denAt M := by
  cases b
  · exact ⟨fun _ => .sym "a", rfl, rfl, by simp [gS]⟩
  · exact ⟨fun _ => .sym "a", rfl, rfl, by simp [gS]⟩

omit [DecidableEq R] in
/-- The ground span has a representative, and it relates the target. -/
theorem rep_g (hL : D.Lawful M) (b : Bool) : ∃ g, D.rep (gS b) = some g ∧ way b ∈ den M g := by
  obtain ⟨g, hg⟩ := rep_exists hL (gS b) (by cases b <;> rfl) ⟨way b, mem_gS b⟩
  exact ⟨g, hg, by rw [hL.rep_some (gS b) g hg]; exact mem_gS b⟩

end

/-! ## The first reading -/

section

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} (K : Kernel R Cost)
  (hK : K.Refines D)

/-- A bound on what the first reading of a member costs, whatever its rank:
the readings of the identity and of the ground span, and the compositions of
their representatives. -/
def fanTicks (D : Domain R) (K : Kernel R Cost) : Nat :=
  match D.rep idS, D.rep (gS false), D.rep (gS true) with
  | some i, some g, some g' =>
    100 + 6 * (K.rep idS).ticks + 4 * (K.compose i i).ticks +
      ((K.rep (gS false)).ticks + (K.compose i g).ticks + 4 * (K.compose g i).ticks) +
      ((K.rep (gS true)).ticks + (K.compose i g').ticks + 4 * (K.compose g' i).ticks)
  | _, _, _ => 0

/-- The union of the ground span and the chain of unions, read by the
number 0: the ground span. -/
theorem reads_Ud {g : R} (b : Bool) (hg : D.rep (gS b) = some g) (d : Nat) :
    Reads Po K hK (d + 2) 0 (Ud m b) ⟨none, Ud m b, none⟩ g 0 (8 + (K.rep (gS b)).ticks) := by
  obtain ⟨p, q, hpq⟩ := bn_isSeq m b
  have hv : (Ud m b).view = .union [.span (gS b), Bn m b] := by
    unfold Ud
    rw [hpq]
    rfl
  have hs := reads_span K hK (P := Po) hg d 0
  obtain ⟨a, h1, h2, h3, h4⟩ := reads_union_zero K hK hv rfl hs rfl rfl
  exact ⟨a, h1, h2, h3, by rw [h4]; simp only [List.length_cons, List.length_nil]; omega⟩

/-- A call of `c`, read by the number 0: the identity. -/
theorem reads_cl (hP : IsFan m Po t) {i : R} (hi : D.rep idS = some i) (f : Bool) (d : Nat) :
    Reads Po K hK (d + 3) 0 (cl f) ⟨none, cl f, none⟩ i 0 (12 + (K.rep idS).ticks) := by
  obtain ⟨p, q, hb⟩ := body_cl hP f
  have hs := reads_span K hK (P := Po) hi d 0
  have hu := reads_union_zero K hK (n := .or I (.seq p q)) (xs := [I, .seq p q]) rfl rfl hs rfl rfl
  have hv : ∃ nm, (cl f).view = .call nm f := by cases f <;> exact ⟨_, rfl⟩
  obtain ⟨nm, hv⟩ := hv
  obtain ⟨a, h1, h2, h3, h4⟩ := reads_call K hK hv hb hu rfl
  exact ⟨a, h1, h2, h3, by rw [h4]; simp only [List.length_cons, List.length_nil]; omega⟩

/-- The chain forwards, read by the number 0: four copies of the identity,
the ground span and the identity, joined. -/
theorem reads_chain_fwd (hP : IsFan m Po t) (hL : D.Lawful Po.sorts.interp) {i g : R}
    (hi : D.rep idS = some i) (hid : den Po.sorts.interp i = {p | p.1 = p.2})
    (hg : D.rep (gS false) = some g) (f : Bool) (d : Nat) :
    ∃ c, Reads Po K hK (d + 4) 0 (mkSeq (chain m false f)) ⟨none, mkSeq (chain m false f), none⟩
        g 0 c ∧
      c ≤ 76 + 5 * (K.rep idS).ticks + 3 * (K.compose i i).ticks + (K.rep (gS false)).ticks +
        (K.compose i g).ticks + (K.compose g i).ticks := by
  have rI := fun k => reads_span K hK (P := Po) hi (d + 2) k
  have rU := reads_Ud (m := m) (Po := Po) K hK false hg (d + 1)
  have rC := reads_cl K hK hP hi f d
  have cii := compose_id_left hL hid i
  have cig := compose_id_left hL hid g
  have cgi := compose_id_right hL hid g
  have hv : (mkSeq (chain m false f)).view = .chain (I :: [I, I, I, Ud m false, cl f]) := by
    cases f <;> rfl
  have j5 := joins_nil K hK (P := Po) (d + 3)
    ⟨none, mkSeq [I, I, I, I, Ud m false, cl f], none⟩ g 0
  have j4 := joins_cons K hK (g₀ := ⟨none, mkSeq [I, I, I, I, Ud m false], none⟩) rC rfl rfl cgi
    (L := 6) (by cases f <;> rfl) (by cases f <;> rfl) j5
  have j3 := joins_cons K hK (g₀ := ⟨none, mkSeq [I, I, I, I], none⟩) rU rfl rfl cig
    (L := 5) rfl rfl j4
  have j2 := joins_cons K hK (g₀ := ⟨none, mkSeq [I, I, I], none⟩) (rI 0) rfl rfl cii
    (L := 4) rfl rfl j3
  have j1 := joins_cons K hK (g₀ := ⟨none, mkSeq [I, I], none⟩) (rI 0) rfl rfl cii
    (L := 3) rfl rfl j2
  have hj := joins_cons K hK (g₀ := ⟨none, I, none⟩) (rI 0) rfl rfl cii (L := 2) rfl rfl j1
  refine ⟨_, reads_chain K hK hv (rI 0) hj (by cases f <;> rfl), ?_⟩
  simp only [List.length_cons, List.length_nil]
  omega

/-- The chain backwards, read by the number 0. -/
theorem reads_chain_bwd (hP : IsFan m Po t) (hL : D.Lawful Po.sorts.interp) {i g : R}
    (hi : D.rep idS = some i) (hid : den Po.sorts.interp i = {p | p.1 = p.2})
    (hg : D.rep (gS true) = some g) (f : Bool) (d : Nat) :
    ∃ c, Reads Po K hK (d + 4) 0 (mkSeq (chain m true f)) ⟨none, mkSeq (chain m true f), none⟩
        g 0 c ∧
      c ≤ 76 + 5 * (K.rep idS).ticks + (K.rep (gS true)).ticks + (K.compose i g).ticks +
        4 * (K.compose g i).ticks := by
  have rI := fun k => reads_span K hK (P := Po) hi (d + 2) k
  have rU := reads_Ud (m := m) (Po := Po) K hK true hg (d + 1)
  have rC := reads_cl K hK hP hi f d
  have cig := compose_id_left hL hid g
  have cgi := compose_id_right hL hid g
  have hv : (mkSeq (chain m true f)).view = .chain (cl f :: [Ud m true, I, I, I, I]) := by
    cases f <;> rfl
  have j5 := joins_nil K hK (P := Po) (d + 3)
    ⟨none, mkSeq [cl f, Ud m true, I, I, I, I], none⟩ g 0
  have j4 := joins_cons K hK (g₀ := ⟨none, mkSeq [cl f, Ud m true, I, I, I], none⟩) (rI 0) rfl rfl
    cgi (L := 6) (by cases f <;> rfl) (by cases f <;> rfl) j5
  have j3 := joins_cons K hK (g₀ := ⟨none, mkSeq [cl f, Ud m true, I, I], none⟩) (rI 0) rfl rfl
    cgi (L := 5) (by cases f <;> rfl) (by cases f <;> rfl) j4
  have j2 := joins_cons K hK (g₀ := ⟨none, mkSeq [cl f, Ud m true, I], none⟩) (rI 0) rfl rfl
    cgi (L := 4) (by cases f <;> rfl) (by cases f <;> rfl) j3
  have j1 := joins_cons K hK (g₀ := ⟨none, mkSeq [cl f, Ud m true], none⟩) (rI 0) rfl rfl
    cgi (L := 3) (by cases f <;> rfl) (by cases f <;> rfl) j2
  have hj := joins_cons K hK (g₀ := ⟨none, cl f, none⟩) rU rfl rfl cig (L := 2)
    (by cases f <;> rfl) (by cases f <;> rfl) j1
  refine ⟨_, reads_chain K hK hv rC hj (by cases f <;> rfl), ?_⟩
  simp only [List.length_cons, List.length_nil]
  omega

/-- **The first reading of a member of the fan** to a depth of five or more
makes an answer of the call of `h` that relates the target, the other way
round when the chain is read backwards, and costs at most `fanTicks`,
whatever the rank. -/
theorem reads_root (hP : IsFan m Po t) (hL : D.Lawful Po.sorts.interp) (c : Bool) (d : Nat) :
    ∃ g cost, way (c ^^ t) ∈ den Po.sorts.interp g ∧
      Reads Po K hK (d + 5) 0 (hl c) ⟨none, hl c, none⟩ g 0 cost ∧ cost ≤ fanTicks D K := by
  obtain ⟨i, hi, hid⟩ := rep_I (D := D) hL
  obtain ⟨gF, hgF, hF⟩ := rep_g (D := D) hL false
  obtain ⟨gT, hgT, hT⟩ := rep_g (D := D) hL true
  have hb := body_hl hP c
  have hv : (hl c).view = .call "h" c := by cases c <;> rfl
  have hW : fanTicks D K = 100 + 6 * (K.rep idS).ticks + 4 * (K.compose i i).ticks +
      ((K.rep (gS false)).ticks + (K.compose i gF).ticks + 4 * (K.compose gF i).ticks) +
      ((K.rep (gS true)).ticks + (K.compose i gT).ticks + 4 * (K.compose gT i).ticks) := by
    simp only [fanTicks, hi, hgF, hgT]
  generalize (c ^^ t) = b at hb ⊢
  cases b
  · obtain ⟨c₀, hr, hc⟩ := reads_chain_fwd K hK hP hL hi hid hgF c d
    exact ⟨gF, _, hF, reads_call K hK hv hb hr rfl, by omega⟩
  · obtain ⟨c₀, hr, hc⟩ := reads_chain_bwd K hK hP hL hi hid hgT c d
    exact ⟨gT, _, hT, reads_call K hK hv hb hr rfl, by omega⟩

end

end Dive

end RwLog
