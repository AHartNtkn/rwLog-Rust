/-
# The kernel rung engines are judged at

`sortsRung` is the kernel rung (`RwLog.KernelRung`,
`lean/RwLog/Trusted/Kernel.lean`) of the domain of sorts whose charges are
derived from the Rust: for the sorts `S` of a program its kernel is
`sortsKernel` (`RwLogVerified/SortsKernel.lean`) at

* `naming`, a naming of the symbols that is one to one and gives the end of
  a list the empty symbol (`naming_inj`, `naming_none`);
* `sortNames S`, the names of the sorts of `S` in order;
* `reachBound S` and `goalBound S`, the most conjunctions and the most goals
  reachable from one in `S`.

The cost of an engine `E` is `E.costed sortsRung`. Each operation of the
rung is realised by the Rust function of its name (`rung_compose_realised`
and the others): the theorems of `SortsKernel.lean`, with no parameter left.
What they assume of the sorts is that no sort has a case for the pair symbol
(`Sorts.NoPair`) and that the store holds their declarations (`Ctx`).

The charges are not computable: a charge is the most the Rust function
spends over the ways its arguments can be held (`most`,
`RwLogVerified/DomChain.lean`).
-/
import RwLogVerified.SortsKernel
import RwLog.Rungs.Symmetric.Rung
import RwLog.Sorts.Dom

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog RwLog.Term

/-- A naming of the symbols: one to one, with the end of a list the empty
symbol. -/
noncomputable def naming : Option Nat → RwLog.Sym := Classical.choose exists_naming

theorem naming_inj : Function.Injective naming := (Classical.choose_spec exists_naming).1

theorem naming_none : naming none = "" := (Classical.choose_spec exists_naming).2

/-- The names of the sorts of `S`, in order. -/
def sortNames (S : Sorts) : List Name := (Sorts.names S).sort (· ≤ ·)

theorem mem_sortNames {S : Sorts} {n : Name} : n ∈ sortNames S ↔ n ∈ Sorts.names S :=
  Finset.mem_sort _

/-- The most conjunctions reachable from one in `S`. -/
noncomputable def reachBound (S : Sorts) : Nat :=
  sSup (Set.range fun c => (Sorts.reachSet S c).card)

/-- The most goals reachable from one in `S`. -/
noncomputable def goalBound (S : Sorts) : Nat :=
  sSup (Set.range fun p : Sorts.Conj × Name => (Sorts.reachGSet S (p.1, some p.2)).card)

theorem reachSet_card_le (S : Sorts) (c : Sorts.Conj) :
    (Sorts.reachSet S c).card ≤ reachBound S := by
  refine le_csSup ⟨(Sorts.names S).powerset.card + 1, ?_⟩ ⟨c, rfl⟩
  rintro _ ⟨d, rfl⟩
  exact (Finset.card_le_card (by unfold Sorts.reachSet; classical exact Finset.filter_subset _ _)).trans
    (Finset.card_insert_le _ _)

theorem reachGSet_card_le (S : Sorts) (d : Sorts.Conj) (m : Name) :
    (Sorts.reachGSet S (d, some m)).card ≤ goalBound S := by
  refine le_csSup ⟨((Sorts.names S).powerset ×ˢ
    insert none ((Sorts.names S).image some)).card + 1, ?_⟩ ⟨(d, m), rfl⟩
  rintro _ ⟨p, rfl⟩
  exact (Finset.card_le_card (by unfold Sorts.reachGSet; classical exact Finset.filter_subset _ _)).trans
    (Finset.card_insert_le _ _)

/-- **The kernel rung of the domain of sorts, every charge derived from the
Rust.** -/
noncomputable def sortsRung : KernelRung where
  Rep := Sorts.Rep
  dom := Sorts.dom
  kernel S := sortsKernel naming S (sortNames S) (reachBound S) (goalBound S)
  refines S := sortsKernel_refines naming S (sortNames S) (reachBound S) (goalBound S)
  lawful _ hS := Sorts.dom_lawful hS

/-! ## Each operation of the rung runs in Rust within its charge -/

section Realised

variable {S : Sorts} {sp : Pat}

theorem rung_rep_realised (hC : Ctx naming S sp (sortNames S)) (hS : S.WellFormed) :
    Realises
      (fun nodes (p : store.TermId × store.TermId × U32 × span.Span) (x : Span) =>
        SortDeclsAt naming sp (sortNames S) nodes p.1 p.2.1 ∧
          naming (some p.2.2.1.val) = neSym ∧ SpanAt naming nodes p.2.2.2 x)
      (OptHeld naming (sortNames S)) (fun s p => dom.rep s p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun x => (sortsRung.kernel S).rep x) :=
  sorts_rep_realised naming_inj naming_none hC hS (fun _ h => mem_sortNames.1 h)
    (reachSet_card_le S) (reachGSet_card_le S)

theorem rung_compose_realised (hC : Ctx naming S sp (sortNames S)) (hN : Sorts.NoPair S) :
    Realises (HeldTwo naming sp (sortNames S)) (OptHeld naming (sortNames S))
      (fun s p => dom.compose s p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun x => (sortsRung.kernel S).compose x.1 x.2) :=
  sorts_compose_realised naming_inj naming_none hC hN (fun _ h => mem_sortNames.1 h)
    (reachSet_card_le S) (reachGSet_card_le S)

theorem rung_meet_realised (hC : Ctx naming S sp (sortNames S)) (hN : Sorts.NoPair S) :
    Realises (HeldTwo naming sp (sortNames S)) (OptHeld naming (sortNames S))
      (fun s p => dom.meet s p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun x => (sortsRung.kernel S).meet x.1 x.2) :=
  sorts_meet_realised naming_inj naming_none hC hN (fun _ h => mem_sortNames.1 h)
    (reachSet_card_le S) (reachGSet_card_le S)

theorem rung_covers_realised (hC : Ctx naming S sp (sortNames S)) (hN : Sorts.NoPair S) :
    Realises (HeldTwo naming sp (sortNames S)) (fun _ (b b' : Bool) => b = b')
      (fun s p => dom.covers s p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun x => (sortsRung.kernel S).covers x.1 x.2) :=
  sorts_covers_realised naming_inj naming_none hC hN (fun _ h => mem_sortNames.1 h)
    (reachSet_card_le S) (reachGSet_card_le S)

theorem rung_eq_realised (hC : Ctx naming S sp (sortNames S)) (hN : Sorts.NoPair S) :
    Realises (HeldTwo naming sp (sortNames S)) (fun _ (b b' : Bool) => b = b')
      (fun s p => dom.eq s p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun x => (sortsRung.kernel S).eq x.1 x.2) :=
  sorts_eq_realised naming_inj naming_none hC hN (fun _ h => mem_sortNames.1 h)
    (reachSet_card_le S) (reachGSet_card_le S)

theorem rung_rightBound_realised (hC : Ctx naming S sp (sortNames S)) (hN : Sorts.NoPair S) :
    Realises (HeldOne naming sp (sortNames S)) (OptHeld naming (sortNames S))
      (fun s p => dom.right s p.1 p.2.1 p.2.2) (fun x => (sortsRung.kernel S).rightBound x) :=
  sorts_rightBound_realised naming_inj naming_none hC hN (fun _ h => mem_sortNames.1 h)
    (reachSet_card_le S) (reachGSet_card_le S)

theorem rung_leftBound_realised (hC : Ctx naming S sp (sortNames S)) (hN : Sorts.NoPair S) :
    Realises (HeldOne naming sp (sortNames S)) (OptHeld naming (sortNames S))
      (fun s p => dom.left s p.1 p.2.1 p.2.2) (fun x => (sortsRung.kernel S).leftBound x) :=
  sorts_leftBound_realised naming_inj naming_none hC hN (fun _ h => mem_sortNames.1 h)
    (reachSet_card_le S) (reachGSet_card_le S)

theorem rung_composable_realised (hC : Ctx naming S sp (sortNames S)) (hN : Sorts.NoPair S) :
    Realises
      (fun nodes (p : store.TermId × store.TermId × store.TermId) (xs : List (Sorts.Rep S)) =>
        SortDeclsAt naming sp (sortNames S) nodes p.1 p.2.1 ∧ ∃ ps : List (Sorts.Rep S × Form),
          ps.map Prod.fst = xs ∧ (∀ x ∈ ps, HeldAs x.1 x.2) ∧
          Repr naming nodes p.2.2.val
            (encList (naming none) (ps.map fun x => packForm naming (sortNames S) x.2)))
      (fun _ (b b' : Bool) => b = b') (fun s p => dom.composable s p.1 p.2.1 p.2.2)
      (fun xs => (sortsRung.kernel S).composable xs) :=
  sorts_composable_realised naming_inj naming_none hC hN (fun _ h => mem_sortNames.1 h)
    (reachSet_card_le S) (reachGSet_card_le S)

end Realised

/-- **Rung 1 has the laws at the kernel rung engines are judged at.** -/
theorem rung1_lawful : Symmetric.rung1.Lawful sortsRung := Symmetric.rung1_lawful sortsRung

/-- **Rung 1 costs the same in both directions at that kernel rung**, within
`12 * (c + n + 1)`. -/
theorem rung1_directionFree (A : ArtifactStore) :
    DirectionFree (Symmetric.rung1.machine sortsRung A) (DirBound.fn ⟨12, 1⟩) :=
  Symmetric.rung1_directionFree sortsRung A

end RwLogVerified
