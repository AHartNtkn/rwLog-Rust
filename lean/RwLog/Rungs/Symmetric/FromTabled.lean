/-
# Where the tabled machine halts, the symmetric engine halts

The tables of a run of the tabled machine that are complete at a round are a
certificate that their goals complete (`tabled_cert`, `Cert` of
`Rungs/Symmetric/Transfer.lean`): they are finitely many; a complete table
holds answers of its goal that cover every answer of the goal; and a table
completes in a round with a strategy all of whose goals are complete after
the round (`Tabled.closes_spec`). That strategy is the reason of the
certificate. A final verdict of the race is completed by every run of the
engine (`final_completes`). The join of a split and a push of the answers of
one side are a split of the engine, because the engine splits a chain at
every interface and the tabled machine at the first and the last, and both
split a meet at the same members; the goals pushed are the same goals; and
the side whose answers are pushed was complete before the round, so it stands
lower in the order of completion.

So with an exact unfolding race that meets its specification, the symmetric
engine halts wherever the mirrored tabled machine halts, which with the raced
unfolding is R005 (`terminatesWhere`).
-/
import RwLog.Rungs.Symmetric.Final
import RwLog.Rungs.Tabled.Mirrored
import RwLog.Rungs.Tabled.EmptySide
import RwLog.Rungs.Tabled.Host

namespace RwLog

namespace Symmetric

open Answer Saturation Goals Unfold

section cert

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  {K : Kernel R Cost} {hK : K.Refines D} {U : GOracle R Rel (Ans D P) Cost}

omit [DecidableEq R] in
/-- The goal the tabled machine pushes to the right side is the engine's. -/
theorem pushLG_eq (g Rg : GoalOf R Rel) (k : Kind) (x : Ans D P) :
    Tabled.pushLG D g Rg k x = pushG D g Rg.node k true x := by
  cases k <;> rfl

omit [DecidableEq R] in
/-- The goal the tabled machine pushes to the left side is the engine's. -/
theorem pushRG_eq (g L : GoalOf R Rel) (k : Kind) (x : Ans D P) :
    Tabled.pushRG D g L k x = pushG D g L.node k false x := by
  cases k <;> rfl

/-- A strategy of a split in the tabled machine is a reason of a certificate,
when its goals are certified no later, the goals complete in the tables
earlier, and the maximal answers the certificate has for a complete goal are
those of its table. -/
theorem why_of_way {ts : List (Tabled.TableOf R Rel (Ans D P))} {g L Rg : GoalOf R Rel} {k : Kind}
    (hsp : SplitAt g k L Rg) {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (Tabled.way (K := DerivationKernel.over D K hK P) ts g (k, L, Rg)).val.2)
    {C : GoalOf R Rel → Prop} {ρ : GoalOf R Rel → Nat} {A : GoalOf R Rel → List (Ans D P)}
    (hdeps : ∀ d ∈ strat, C d ∧ ρ d ≤ ρ g)
    (hlow : ∀ d, Tabled.isDone ts d = true → ρ d < ρ g)
    (hmax : ∀ d, Tabled.isDone ts d = true → ∀ x' ∈ (A d).maximaBy (covB D P),
      ∃ x ∈ (Tabled.ansOf ts d).maximaBy (covB D P), x.span = x'.span) :
    Why C ρ A g := by
  rcases (Tabled.mem_way_strats K hK ts g (k, L, Rg) strat).1 hs with rfl | ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · exact .join k L Rg hsp (hdeps L (by simp)) (hdeps Rg (by simp))
  · refine .push k L Rg true hsp ⟨(hdeps L (by simp)).1, hlow L hd⟩ fun x' hx' => ?_
    obtain ⟨x, hx, e⟩ := hmax L hd x' hx'
    have := hdeps (Tabled.pushLG D g Rg k x)
      (List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩))
    rw [Tabled.pushLG_span g Rg k e, pushLG_eq] at this
    exact this
  · refine .push k L Rg false hsp ⟨(hdeps Rg (by simp)).1, hlow Rg hd⟩ fun x' hx' => ?_
    obtain ⟨x, hx, e⟩ := hmax Rg hd x' hx'
    have := hdeps (Tabled.pushRG D g L k x)
      (List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩))
    rw [Tabled.pushRG_span g L k e, pushRG_eq] at this
    exact this

/-- **The complete tables of a run of the tabled machine are a certificate
that their goals complete**, with the answers of the tables and the round of
completion as the order. -/
theorem tabled_cert (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) (hU : UOk D P U)
    (hE : UEx D P U) {root : Rel} (hroot : GoalOk D (⟨none, root, none⟩ : GoalOf R Rel))
    (N : Nat) :
    ∃ (ρ : GoalOf R Rel → Nat) (A : GoalOf R Rel → List (Ans D P)),
      Cert U (fun g => Tabled.isDone (Tabled.tablesAt K hK U root N) g = true) ρ A := by
  classical
  have hI := Tabled.inv_at hL hP hU hroot (K := K) (hK := hK)
  let ρ : GoalOf R Rel → Nat := fun g =>
    if h : ∃ r, Tabled.isDone (Tabled.tablesAt K hK U root r) g = true then Nat.find h else 0
  have hρle : ∀ d r, Tabled.isDone (Tabled.tablesAt K hK U root r) d = true → ρ d ≤ r := by
    intro d r h
    have hex : ∃ r, Tabled.isDone (Tabled.tablesAt K hK U root r) d = true := ⟨r, h⟩
    simp only [ρ, hex, ↓reduceDIte]
    exact Nat.find_min' hex h
  refine ⟨ρ, fun g => Tabled.ansOf (Tabled.tablesAt K hK U root N) g, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact ⟨(Tabled.tablesAt K hK U root N).map (·.goal), fun g hg => by
      obtain ⟨t, ht, e⟩ := Tabled.idx_isSome.1 (Tabled.idx_of_done hg)
      exact List.mem_map.2 ⟨t, ht, e⟩⟩
  · exact fun g _ a ha => Tabled.ansOf_goal (hI N).ok ha
  · exact fun g hg y hy => Tabled.done_covers hL (hI N) hg hy
  · intro g hg
    have hex : ∃ r, Tabled.isDone (Tabled.tablesAt K hK U root r) g = true := ⟨N, hg⟩
    have hρ : ρ g = Nat.find hex := by simp only [ρ, hex, ↓reduceDIte]
    have hspec := Nat.find_spec hex
    have hmin : ∀ r, Tabled.isDone (Tabled.tablesAt K hK U root r) g = true →
        Nat.find hex ≤ r := fun r h => Nat.find_min' hex h
    generalize Nat.find hex = m at hρ hspec hmin
    cases m with
    | zero => rw [Tabled.not_done_zero] at hspec; cases hspec
    | succ r =>
      have hrN : r + 1 ≤ N := hmin N hg
      rcases Tabled.done_step hspec with h | hc
      · have := hmin r h
        omega
      obtain ⟨⟨i, hi⟩, -, -, strat, hs, hdeps⟩ := Tabled.closes_spec hc
      obtain ⟨hil, hgg, -⟩ := Tabled.idx_some.1 hi
      have hgok : GoalOk D g := hgg ▸ ((hI r).ok _ (List.getElem_mem hil)).1
      have dep : ∀ d ∈ strat, Tabled.isDone (Tabled.tablesAt K hK U root N) d = true ∧
          ρ d ≤ ρ g := fun d hd => by
        obtain ⟨⟨j, hj⟩, hc'⟩ := hdeps d hd
        have h1 : Tabled.isDone (Tabled.tablesAt K hK U root (r + 1)) d = true :=
          (Tabled.isDone_next hj).2 hc'
        exact ⟨Tabled.done_mono hrN h1, by rw [hρ]; exact hρle d _ h1⟩
      have low : ∀ d, Tabled.isDone (Tabled.tablesAt K hK U root r) d = true → ρ d < ρ g :=
        fun d h => by rw [hρ]; exact Nat.lt_succ_of_le (hρle d r h)
      have hmax : ∀ d, Tabled.isDone (Tabled.tablesAt K hK U root r) d = true →
          ∀ x' ∈ (Tabled.ansOf (Tabled.tablesAt K hK U root N) d).maximaBy (covB D P),
          ∃ x ∈ (Tabled.ansOf (Tabled.tablesAt K hK U root r) d).maximaBy (covB D P),
            x.span = x'.span := fun d hd =>
        maxima_same hL
          (fun a ha => Tabled.done_covers hL (hI r) hd (Tabled.ansOf_goal (hI N).ok ha))
          (fun a ha => Tabled.done_covers hL (hI N) (Tabled.done_mono (by omega) hd)
            (Tabled.ansOf_goal (hI r).ok ha))
      rcases (Tabled.mem_prodG_snd K hK U _ r g strat).1 hs with ⟨hv, rfl⟩ | hs'
      · exact .inl (final_completes hL hP hU hE r g hgok hv)
      · right
        cases hv : g.node.view.forget with
        | span u => exact .span (forget_span hv)
        | call n f =>
          obtain ⟨b, hb⟩ := forget_call (P := P) hv
          rw [Tabled.produceTables_call K hK _ g hv hb] at hs'
          obtain rfl : strat = [⟨g.lb, b, g.rb⟩] := by simpa using hs'
          refine .copy true (fun _ => ⟨b, hb⟩) (fun h => by cases h) (fun x hx => ?_)
          have hx' : x ∈ (Charged.bodyOf P g.node).toList := hx
          rw [hb] at hx'
          obtain rfl : x = b := by simpa using hx'
          exact dep _ (by simp)
        | union xs =>
          have hvu := forget_union hv
          have hparts : xs = g.node.unionParts := hgok.normal.view_union_eq hvu
          rw [Tabled.produceTables_union K hK _ g hv] at hs'
          obtain rfl : strat = xs.map fun x => ⟨g.lb, x, g.rb⟩ := by simpa using hs'
          refine .copy false (fun h => by cases h) (fun _ => ⟨xs, hvu⟩) (fun x hx => ?_)
          have hx' : x ∈ g.node.unionParts := hx
          rw [← hparts] at hx'
          exact dep _ (List.mem_map.2 ⟨x, hx', rfl⟩)
        | chain xs =>
          have hvc := forget_chain hv
          obtain ⟨h2, -, -⟩ := hgok.normal.view_chain hvc
          rw [Tabled.produceTables_chain K hK _ g hv] at hs'
          obtain ⟨_, hr, hs'⟩ := List.mem_flatMap.1 hs'
          obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
          obtain ⟨i, hi', l, rr, hl, hrr, rfl⟩ := (Tabled.mem_splitsOf_chain K hK g xs w).1 hw
          obtain ⟨h0, hlt⟩ := Tabled.mem_seqSplits h2 hi'
          have hsp : SplitAt g .seq ⟨g.lb, l, none⟩ ⟨none, rr, g.rb⟩ :=
            ⟨xs, i, l, rr, hvc, h0, hlt, hl, hrr, rfl, rfl⟩
          exact why_of_way hsp hs' dep low hmax
        | meet xs =>
          have hvm := forget_meet hv
          rw [Tabled.produceTables_meet K hK _ g hv] at hs'
          obtain ⟨_, hr, hs'⟩ := List.mem_flatMap.1 hs'
          obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
          obtain ⟨i, hi', l, rr, hl, hrr, rfl⟩ := (Tabled.mem_splitsOf_meet K hK g xs w).1 hw
          have hsp : SplitAt g .and ⟨g.lb, l, g.rb⟩ ⟨g.lb, rr, g.rb⟩ :=
            ⟨xs, i, l, rr, hvm, hi', hl, hrr, rfl, rfl⟩
          exact why_of_way hsp hs' dep low hmax

end cert

section theorems

variable {U : Unfolder} {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  {dom : ∀ S, Domain (R S)} {K : ∀ S, Kernel (R S) Cost} {hK : ∀ S, (K S).Refines (dom S)}

/-- **The symmetric engine halts wherever the mirrored tabled machine
halts**, with an exact unfolding race that meets its specification. -/
theorem terminatesWhere (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)
    (hG : RwLog.Good @U) (hE : Exact @U) :
    (Rt @U dom K hK).TerminatesWhere (Tabled.Mt @U dom K hK) := by
  intro P q wf ⟨n, hn⟩
  have hL := hD _ wf.2.2.1
  have hfo := wf.progFO
  obtain ⟨r, hr⟩ := (Tabled.terminates_iff (K := K) (hK := hK) hD hG wf).1
    ⟨n, (Tabled.mirror_halts hD hG hE wf n).1 hn⟩
  obtain ⟨ρ, A, hC⟩ := tabled_cert (K := K P.sorts) (hK := hK P.sorts) hL hfo
    (hG (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hfo)
    (hE (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hfo) (Tabled.root_ok wf) r
  have hτ := isRun_of_wf (K := K) (hK := hK) hD hG wf
  refine (terminates_iff (K := K) (hK := hK) hD hG wf).2 ?_
  exact hC.completes hL hr _ hτ (fun r j => nocov_stateAt r j) 0 0 root_goal0
    (hτ.opened_of_settled root_goal0 fun r' => ⟨r', Nat.le_refl _, (hτ.req.req r').root⟩)

end theorems

end Symmetric

end RwLog
