/-
# Rung 2

The second rung is the symmetric engine of rung 1 with the diving engine
beside it (`Engine.beside`), run on one orientation of its input. At every
kernel rung:

* it has the laws (`rung2_lawful`): it is complete and honest when it is
  done because rung 1 is, and sound because every engine is;
* it reports that it is done exactly where rung 1 does (`rung2_halts`);
* its cost does not depend on the direction an input is written in
  (`rung2_directionFree`);
* on a member of the fan (`Symmetric.Fan.cls`) of rank `k` it covers the
  target having paid at most `rung2Hi κ * (k + 1) ^ 2` ticks
  (`rung2_alone`), where rung 1 has paid `2 ^ k` (`Symmetric.Fan.below`).
-/
import RwLog.Rungs.Dive.Converse
import RwLog.Rungs.Symmetric.FanClass

open RwLog.Symmetric RwLog.Symmetric.Fan

namespace RwLog

namespace Symmetric

section

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} (K : Kernel R Cost)
  (hK : K.Refines D) {P : Program}

/-- Building the first state of the symmetric engine costs two ticks. -/
theorem init_ticks (root : Rel) :
    (init (K := DerivationKernel.over D K hK P) root).ticks = 2 := by
  at_cost K hK
  simp [init, selfConverse, sameBound, Cost.bind_ticks, Charged.eqNode]
  rfl

end

end Symmetric

namespace Dive

/-- Rung 2: the symmetric engine of rung 1 with the diving engine beside it,
run on one orientation of the input. -/
def rung2 : CostedRung := ⟨[], (engine Unfold.raced @runsReader).beside dive, true⟩

/-- The engine of rung 1. -/
abbrev eng1 : Engine := engine Unfold.raced @runsReader

/-- **Rung 2 has the laws.** -/
theorem rung2_lawful (κ : KernelRung) : rung2.Lawful κ := fun _ =>
  CostedRuntime.oriented_laws
    (Engine.sound (eng1.beside dive) κ.dom κ.kernel κ.refines κ.lawful)
    (Engine.beside_complete eng1 dive κ.dom κ.kernel κ.refines κ.cells
      (complete (U := Unfold.raced) (rd := @runsReader) (dom := κ.dom) (K := κ.kernel)
        (hK := κ.refines) κ.lawful good_raced good_runsReader))
    (Engine.beside_honest eng1 dive κ.dom κ.kernel κ.refines κ.cells
      (Engine.sound (eng1.beside dive) κ.dom κ.kernel κ.refines κ.lawful)
      (honestExhaustion (U := Unfold.raced) (rd := @runsReader) (dom := κ.dom) (K := κ.kernel)
        (hK := κ.refines) κ.lawful good_raced good_runsReader))

/-- **Rung 2 costs the same in both directions**, within
`12 * (c + n + 1)`. -/
theorem rung2_directionFree (κ : KernelRung) (A : ArtifactStore) :
    DirectionFree (rung2.machine κ A) (DirBound.fn ⟨12, 1⟩) :=
  CostedRuntime.oriented_directionFree_bound
    (C := (eng1.beside dive).costedAt κ.dom κ.kernel κ.refines κ.cells)
    (Engine.beside_selfConverse eng1 dive κ.dom κ.kernel κ.refines κ.cells
      (engine_selfConverse (U := Unfold.raced) (rd := @runsReader) (dom := κ.dom)
        (K := κ.kernel) (hK := κ.refines) κ.lawful good_raced good_runsReader)
      (dive_selfConverse κ.dom κ.kernel κ.refines κ.cells))

/-- **Rung 2 reports that it is done on every input on which rung 1
does.** -/
theorem rung2_halts (κ : KernelRung) (A : ArtifactStore) (P : Program) (q : Rel)
    (h : (rung1.machine κ A).runtime.Terminates P q) :
    (rung2.machine κ A).runtime.Terminates P q := by
  obtain ⟨n, hn⟩ := h
  have h1 := (CostedRuntime.oriented_init_halts
    (eng1.costedAt κ.dom κ.kernel κ.refines κ.cells) P q n).1 hn
  obtain ⟨m, hm⟩ := (Engine.beside_terminates eng1 dive κ.dom κ.kernel κ.refines κ.cells _ _).2
    ⟨n, h1⟩
  exact ⟨m, (CostedRuntime.oriented_init_halts
    ((eng1.beside dive).costedAt κ.dom κ.kernel κ.refines κ.cells) P q m).2 hm⟩

/-! ## The fan alone -/

/-- The bodies of a member of the fan are in normal form. -/
theorem normed_prog (m : Nat) : (prog m).normed = prog m := by
  have e1 : (body m).norm = body m := by
    rw [show (body m).norm = nmap false false (body m) from rfl, nmap_body]; rfl
  have e2 : cbody.norm = cbody := by
    rw [show cbody.norm = nmap false false cbody from rfl, nmap_cbody]; rfl
  show (⟨[("h", (body m).norm), ("c", cbody.norm)], []⟩ : Program) = _
  rw [e1, e2]; rfl

theorem cmp_prog (m : Nat) : listCmp relCmp ((prog m).defs.map fun d => d.2.norm)
    ((prog m).dual.defs.map fun d => d.2.norm) = .lt := by
  have e1 : (body m).norm = mkSeq (chain m false false) := by
    rw [show (body m).norm = nmap false false (body m) from rfl, nmap_body]; rfl
  have e2 : (body m).dual.norm = mkSeq (chain m true false) := by
    rw [← nmap_tt, nmap_body]; rfl
  show listCmp relCmp [(body m).norm, cbody.norm] [(body m).dual.norm, cbody.dual.norm] = .lt
  rw [e1, e2]; rfl

theorem pick_h (Pn : Program) :
    pick Pn ((RelOf.call "h" : Rel), false) [(RelOf.conv (.call "h"), true)] =
      ⟨true, Pn, .conv (.call "h")⟩ := by
  have hl : leastRel (RelOf.call "h" : Rel) [RelOf.conv (.call "h")] = .conv (.call "h") := by
    decide
  unfold pick; simp only [List.map, hl]; rfl

/-- **The orientation a member of the fan is run in**: the member itself,
from the converse of `h`, so that the body is read from its end. -/
theorem orient_prog (m : Nat) :
    orient (prog m) (.call "h") = ⟨true, prog m, .conv (.call "h")⟩ := by
  unfold orient; rw [cmp_prog, normed_prog]; exact pick_h _

theorem isFan_prog (m : Nat) : IsFan m (prog m) false :=
  ⟨rfl, by rw [nmap_body]; rfl, rfl⟩

/-- What a machine run on one orientation has paid: the charge of choosing
the input, and what the machine has paid on the chosen input. -/
theorem oriented_paid (C : CostedRuntime) (P : Program) (q : Rel) (n : Nat) :
    C.oriented.paid P q n =
      4 * (P.size + q.size + 1) ^ 2 + C.paid (orient P q).P (orient P q).root n := by
  unfold CostedRuntime.paid
  rw [CostedRuntime.oriented_init_ticks, CostedRuntime.oriented_start,
    CostedRuntime.oriented_spent]
  omega

/-- The budget the diving engine's first reading of a member fits at the
kernel rung `κ`, as an exponent. It does not depend on the rank. -/
def fanW (κ : KernelRung) : Nat := fanLevel (fanTicks (κ.dom []) (κ.kernel []))

/-- The coefficient of the bound on what rung 2 has paid when it covers the
target of a member of the fan, at the kernel rung `κ`. -/
def rung2Hi (κ : KernelRung) : Nat :=
  242406 + (60 * ((fanW κ * fanW κ + 1) * (2 ^ fanW κ + 3)) + 20 * (fanW κ * fanW κ + 1) + 18)

/-- **On a member of the fan of rank `k`, rung 2 covers the target having
paid at most `rung2Hi κ * (k + 1) ^ 2` ticks.** The diving engine makes an
answer that relates the target by its first reading, within a budget that
does not depend on the rank; the pair has emitted it, or is done and has
emitted an answer that relates the target, having paid a fixed multiple of
what the diving engine spent. The rest is the charge of choosing and loading
the input, which is quadratic in its size. -/
theorem rung2_alone (κ : KernelRung) (A : ArtifactStore) (P : Program) (r : Rel)
    (hm : cls.mem P r) (x : GTerm × GTerm) (hx : x ∈ cls.tgt P r) :
    (rung2.machine κ A).CoversUsing Resource.time.meter P r P.sorts.interp x
      (rung2Hi κ * (cls.rank P r + 1) ^ 2) := by
  have hsize := Fan.proper.size_le P r hm
  obtain ⟨rfl, hP⟩ := mem_cls hm
  obtain rfl : x = target := by simpa [cls] using hx
  generalize cls.rank P (.call "h") = k at hP hsize ⊢
  subst hP
  have e : rung2.machine κ A =
      ((eng1.beside dive).costedAt κ.dom κ.kernel κ.refines κ.cells).oriented.reLive
        (rung2.machine κ A).live := rfl
  suffices h : ((eng1.beside dive).costedAt κ.dom κ.kernel κ.refines κ.cells).oriented.CoversUsing
      Meter.time (prog k) (.call "h") (prog k).sorts.interp target
      (rung2Hi κ * (k + 1) ^ 2) by
    obtain ⟨n, hc, hp⟩ := h
    rw [e]
    exact ⟨n, hc, le_of_eq_of_le (CostedRuntime.paid_reLive _ _ _ _ _) hp⟩
  have ho := orient_prog k
  have hL : (κ.dom (prog k).sorts).Lawful (prog k).sorts.interp :=
    κ.lawful _ Sorts.wellFormed_nil
  obtain ⟨n, g, hway, hem, hn, hsp⟩ :=
    dive_fan κ.dom κ.kernel κ.refines κ.cells (isFan_prog k) hL true
  obtain ⟨m', hpaid, hor⟩ :=
    Engine.beside_paid eng1 dive κ.dom κ.kernel κ.refines κ.cells (prog k) (hl true) n
  have hi1 : ((eng1.costedAt κ.dom κ.kernel κ.refines κ.cells).init (prog k) (hl true)).ticks =
      ((prog k).size + (hl true).size) ^ 2 + 2 := by
    show (Charged.load (prog k) (hl true) >>= fun root =>
      (Symmetric.init (K := DerivationKernel.over (κ.dom (prog k).sorts) (κ.kernel (prog k).sorts)
        (κ.refines (prog k).sorts) (prog k)) root) >>= fun st =>
        pure (⟨prog k, root, st⟩ : eng1.StateAt κ.dom)).ticks = _
    simp only [Cost.bind_ticks, Cost.pure_ticks, Symmetric.init_ticks]
    rfl
  have hi2 := dive_init_ticks κ.dom κ.kernel κ.refines κ.cells (prog k) (hl true)
  refine ⟨m', ?_, ?_⟩
  · show ∃ a ∈ ((eng1.beside dive).costedAt κ.dom κ.kernel κ.refines κ.cells).oriented.runtime.emitted
      (((eng1.beside dive).costedAt κ.dom κ.kernel κ.refines κ.cells).oriented.runtime.init
        (prog k) (.call "h")) m', target ∈ Answer.den (prog k).sorts.interp a
    rcases hor with hh | hall
    · have hlaws := rung2_lawful κ A
      have hhalt := (CostedRuntime.oriented_init_halts
        ((eng1.beside dive).costedAt κ.dom κ.kernel κ.refines κ.cells) (prog k) (.call "h") m').2
        (by rw [ho]; exact hh)
      have hpairs := hlaws.honest (prog k) (.call "h") (wf_prog k) m' hhalt
      have ht := related_prog k
      rw [hpairs] at ht
      obtain ⟨a, ha, hta⟩ := Set.mem_iUnion₂.1 ht
      exact ⟨a, ha, hta⟩
    · rw [CostedRuntime.oriented_init_emitted, ho]
      refine ⟨Answer.as true (⟨(prog k).sorts, g⟩ : (S : Sorts) × κ.Rep S),
        List.mem_map.2 ⟨_, hall _ hem, rfl⟩, ?_⟩
      show target ∈ Answer.den (prog k).sorts.interp
        (Answer.as true (⟨(prog k).sorts, g⟩ : (S : Sorts) × κ.Rep S))
      rw [Answer.den_as]
      exact hway
  · show ((eng1.beside dive).costedAt κ.dom κ.kernel κ.refines κ.cells).oriented.paid
      (prog k) (.call "h") m' ≤ _
    rw [oriented_paid, ho]
    show 4 * ((prog k).size + (RelOf.call "h" : Rel).size + 1) ^ 2 +
      ((eng1.beside dive).costedAt κ.dom κ.kernel κ.refines κ.cells).paid (prog k) (hl true) m' ≤ _
    have hW : fanLevel (fanTicks (κ.dom (prog k).sorts) (κ.kernel (prog k).sorts)) = fanW κ := rfl
    rw [hW] at hn hsp
    have hs' : (prog k).size + (hl true).size = (prog k).size + (RelOf.call "h" : Rel).size + 1 :=
      rfl
    rw [hi1, hi2, hs'] at hpaid
    rw [pow_one] at hsize
    generalize (prog k).size + (RelOf.call "h" : Rel).size = s at hsize hpaid ⊢
    generalize (dive.costedAt κ.dom κ.kernel κ.refines κ.cells).spent _ n = sp at hsp hpaid
    generalize ((eng1.beside dive).costedAt κ.dom κ.kernel κ.refines κ.cells).paid _ _ m' = pd
      at hpaid ⊢
    have h1 : (s + 1) ^ 2 ≤ (201 * (k + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : (201 * (k + 1)) ^ 2 = 40401 * (k + 1) ^ 2 := by ring
    have h3 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    unfold rung2Hi
    rw [Nat.add_mul]
    generalize hc : 60 * ((fanW κ * fanW κ + 1) * (2 ^ fanW κ + 3)) + 20 * (fanW κ * fanW κ + 1) +
      18 = c
    have h4 : c ≤ c * (k + 1) ^ 2 := Nat.le_mul_of_pos_right _ h3
    generalize c * (k + 1) ^ 2 = cz at h4 ⊢
    generalize (fanW κ * fanW κ + 1) * (2 ^ fanW κ + 3) = w1 at hsp hc
    generalize fanW κ * fanW κ = w2 at hn hc
    generalize (s + 1) ^ 2 = S2 at hpaid h1 ⊢
    omega

end Dive

end RwLog
