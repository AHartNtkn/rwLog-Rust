/-
# Whether the members of some sorts are the instances of a pattern

`fitsIn S c K p` decides whether every member of the sorts `K` is an instance
of the pattern `p` with its variables in the sorts `c` gives them
(`fitsIn_iff`), for a first-order pattern with no variable twice of which some
such instance is in `K`. It asks the roots of `K` and the sorts of its
arguments, one symbol of the pattern at a time, and nothing of the members.
-/
import RwLog.Sorts.Free
import RwLog.Sorts.Roots
import RwLog.Sorts.Tight

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts}

/-- A term with a head symbol is that symbol applied to its arguments, each
smaller, and each first-order when the term is. -/
theorem Term.spine_some {V : Type} : ∀ {t : Term V} {f : Sym} {as : List (Term V)},
    t.spine = some (f, as) → t = Term.mk f as ∧ (∀ a ∈ as, a.size < t.size) ∧
      (t.firstOrder = true → ∀ a ∈ as, a.firstOrder = true)
  | .var _, _, _, h => by simp [Term.spine] at h
  | .sym g, f, as, h => by
    simp only [Term.spine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp, by simp⟩
  | .app t u, f, as, h => by
    simp only [Term.spine, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨g, bs⟩, hs, rfl, rfl⟩ := h
    obtain ⟨e, hsz, hfo⟩ := Term.spine_some hs
    refine ⟨by rw [e]; simp [Term.mk], fun a ha => ?_, fun h a ha => ?_⟩
    · simp only [List.mem_append, List.mem_singleton] at ha
      simp only [Term.size]
      rcases ha with ha | rfl
      · have := hsz a ha
        omega
      · omega
    · obtain ⟨h1, h2, -⟩ := Term.fo_app h
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hfo h1 a ha
      · exact h2

/-- Every member of the sorts `K` is an instance of the pattern with its
variables in their sorts: a variable when `K` is within its sorts, a symbol
applied to arguments when the members of `K` have that one root and each
argument fits the sorts `K` gives it. -/
def fitsIn (S : Sorts) (c : Nat → Conj) (K : Conj) (p : Pat) : Bool :=
  match hp : p.spine with
  | none =>
    match p with
    | .var y => decide (∀ m ∈ c y, Incl S K m)
    | _ => false
  | some (f, as) =>
    decide (sole S K [] = some (f, as.length)) &&
      (List.finRange as.length).all fun i => fitsIn S c (kidC S K f as.length i) as[i]
termination_by p.size
decreasing_by exact (Term.spine_some hp).2.1 _ (List.getElem_mem _)

theorem fitsIn_var (c : Nat → Conj) (K : Conj) (y : Nat) :
    fitsIn S c K (.var y) = decide (∀ m ∈ c y, Incl S K m) := by
  rw [fitsIn]
  split
  · rfl
  · rename_i h
    simp [Term.spine] at h

theorem fitsIn_mk (c : Nat → Conj) (K : Conj) (f : Sym) (as : List Pat) :
    fitsIn S c K (Term.mk f as) =
      (decide (sole S K [] = some (f, as.length)) &&
        (List.finRange as.length).all fun i => fitsIn S c (kidC S K f as.length i) as[i]) := by
  rw [fitsIn]
  split
  · rename_i h
    rw [Term.spine_mk] at h
    cases h
  · rename_i g bs h
    rw [Term.spine_mk] at h
    cases h
    rfl

/-- Arguments that share no variable: a variable is in one of them. -/
theorem vars_disjoint_of_nodup {as : List Pat} (h : (as.flatMap Term.vars).Nodup) {i j : Nat}
    (hi : i < as.length) (hj : j < as.length) {y : Nat} (h₁ : y ∈ as[i].vars)
    (h₂ : y ∈ as[j].vars) : i = j := by
  have hp := (List.nodup_flatMap.1 h).2
  rw [List.pairwise_iff_getElem] at hp
  rcases Nat.lt_trichotomy i j with hlt | e | hlt
  · exact absurd h₂ (fun hc => hp i j hi hj hlt h₁ hc)
  · exact e
  · exact absurd h₁ (fun hc => hp j i hj hi hlt h₂ hc)

/-- `fitsIn` is exact for a first-order pattern with no variable twice of
which some instance, with its variables in their sorts, is in `K`. -/
theorem fitsIn_iff (hS : S.WellFormed) (c : Nat → Conj) : ∀ (k : Nat) (p : Pat), p.size = k →
    ∀ K : Conj, p.firstOrder = true → p.vars.Nodup → ∀ σ₀ : Nat → GTerm,
    (∀ y ∈ p.vars, MemC S (c y) (σ₀ y)) → MemC S K (p.bind σ₀) →
    (fitsIn S c K p = true ↔
      ∀ h, MemC S K h → ∃ σ : Nat → GTerm, (∀ y ∈ p.vars, MemC S (c y) (σ y)) ∧ p.bind σ = h) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro p hk K hfo hnd σ₀ hσ₀ hm₀
    cases hsp : p.spine with
    | none =>
      cases p with
      | var y =>
        rw [fitsIn_var, decide_eq_true_iff]
        constructor
        · intro h g hg
          refine ⟨fun _ => g, fun y' hy' => ?_, rfl⟩
          simp only [Term.vars, List.mem_singleton] at hy'
          subst hy'
          exact fun m hm => h m hm g hg
        · intro h m hm t ht
          obtain ⟨σ, hσ, e⟩ := h t ht
          have := hσ y (by simp [Term.vars]) m hm
          rw [← e]
          exact this
      | sym f => simp [Term.spine] at hsp
      | app a b =>
        have := Term.key_isSome hfo (by simp)
        simp [Term.key, hsp] at this
    | some fa =>
      obtain ⟨f, as⟩ := fa
      obtain ⟨rfl, hsz, hfoa⟩ := Term.spine_some hsp
      have hbind : ∀ σ : Nat → GTerm,
          (Term.mk f as).bind σ = Term.mk f (as.map (Term.bind σ)) := fun σ => Term.bind_mk σ f as
      have hvars : (Term.mk f as).vars = as.flatMap Term.vars := Term.vars_mk f as
      have hkey : ∀ σ : Nat → GTerm, ((Term.mk f as).bind σ).key = some (f, as.length) :=
        fun σ => by rw [hbind]; simp [Term.key, Term.spine_mk]
      have hm₁ := hm₀
      rw [hbind] at hm₁
      obtain ⟨hacc, hkids⟩ := memC_mk.1 hm₁
      simp only [List.length_map] at hacc hkids
      rw [hvars] at hnd hσ₀
      have hsub : ∀ (i : Nat) (hi : i < as.length), ∀ y ∈ as[i].vars,
          y ∈ as.flatMap Term.vars :=
        fun i hi y hy => List.mem_flatMap.2 ⟨as[i], List.getElem_mem hi, hy⟩
      have hih : ∀ (i : Nat) (hi : i < as.length),
          (fitsIn S c (kidC S K f as.length i) as[i] = true ↔
            ∀ h, MemC S (kidC S K f as.length i) h →
              ∃ σ : Nat → GTerm, (∀ y ∈ as[i].vars, MemC S (c y) (σ y)) ∧ as[i].bind σ = h) :=
        fun i hi => ih _ (hk ▸ hsz _ (List.getElem_mem hi)) _ rfl _
          (hfoa hfo _ (List.getElem_mem hi))
          ((List.nodup_flatMap.1 hnd).1 _ (List.getElem_mem hi)) σ₀
          (fun y hy => hσ₀ y (hsub i hi y hy))
          (by simpa using hkids i (by simpa using hi))
      rw [fitsIn_mk, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]
      constructor
      · rintro ⟨hsole, hall⟩ h hh
        obtain ⟨hs, rfl, hlen⟩ := key_eq_mk (sole_sound hsole hh (by simp))
        obtain ⟨-, hhk⟩ := memC_mk.1 hh
        have hex : ∀ i : Fin as.length, ∃ σ : Nat → GTerm,
            (∀ y ∈ as[i].vars, MemC S (c y) (σ y)) ∧ as[i].bind σ = hs[i]'(by rw [hlen]; exact i.2) :=
          fun i => (hih i i.2).1 (hall i (List.mem_finRange i)) _
            (by simpa [hlen] using hhk i (by rw [hlen]; exact i.2))
        choose σs hσs using hex
        classical
        let σ : Nat → GTerm := fun y =>
          if hy : ∃ i : Fin as.length, y ∈ as[i].vars then σs (Classical.choose hy) y else σ₀ y
        have hσeq : ∀ (i : Fin as.length), ∀ y ∈ as[i].vars, σ y = σs i y := by
          intro i y hy
          have hex' : ∃ i : Fin as.length, y ∈ as[i].vars := ⟨i, hy⟩
          have hc := Classical.choose_spec hex'
          have : Classical.choose hex' = i :=
            Fin.ext (vars_disjoint_of_nodup hnd (Classical.choose hex').2 i.2 hc hy)
          simp only [σ, hex', ↓reduceDIte, this]
        refine ⟨σ, fun y hy => ?_, ?_⟩
        · rw [hvars] at hy
          obtain ⟨a, ha, hya⟩ := List.mem_flatMap.1 hy
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
          rw [hσeq ⟨i, hi⟩ y hya]
          exact (hσs ⟨i, hi⟩).1 y hya
        · rw [hbind]
          congr 1
          apply List.ext_getElem (by simp [hlen])
          intro i h₁ h₂
          have hi : i < as.length := by simpa using h₁
          rw [List.getElem_map]
          exact (Term.bind_congr fun y hy => hσeq ⟨i, hi⟩ y hy).trans (hσs ⟨i, hi⟩).2
      · intro hsem
        refine ⟨?_, fun i _ => ?_⟩
        · cases hsl : sole S K [] with
          | none =>
            obtain ⟨t₁, t₂, h₁, -, h₂, -, hne⟩ := sole_none hS hsl hm₀ (by simp)
            obtain ⟨σ₁, -, rfl⟩ := hsem t₁ h₁
            obtain ⟨σ₂, -, rfl⟩ := hsem t₂ h₂
            rw [hkey, hkey] at hne
            exact absurd rfl hne
          | some key =>
            have := sole_sound hsl hm₀ (by simp)
            rw [hkey] at this
            rw [this]
        · refine (hih i i.2).2 fun h hh => ?_
          have hmem : MemC S K (Term.mk f ((as.map (Term.bind σ₀)).set i h)) := by
            refine memC_mk.2 ⟨by simpa using hacc, fun j hj => ?_⟩
            have hj' : j < as.length := by simpa using hj
            simp only [List.length_set, List.length_map, List.getElem_set]
            split
            · rename_i e
              rw [← e]
              exact hh
            · simpa using hkids j hj'
          obtain ⟨σ, hσ, e⟩ := hsem _ hmem
          rw [hbind] at e
          have e' := congrArg (fun l : List GTerm => l[(i : Nat)]?) (Term.mk_inj e).2
          refine ⟨σ, fun y hy => hσ y (by rw [hvars]; exact hsub i i.2 y hy), ?_⟩
          simpa using e'

/-! ## The sorts of a subterm -/

/-- The sorts pushed down a pattern are on its variables. -/
theorem pushK_vars : ∀ (p : Pat) (n : Name) (extra : Nat) (ks : List (Option Name)) (as : Atoms),
    pushK S p n extra = some (ks, as) → ∀ a ∈ as, a.1 ∈ p.vars
  | .var x, n, _, ks, as, h => by
    simp only [pushK, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [Term.vars]
  | .sym f, n, extra, ks, as, h => by
    simp only [pushK, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, -, -, rfl⟩ := h
    simp
  | .app t u, n, extra, ks, as, h => by
    simp only [pushK] at h
    cases hk : pushK S t n (extra + 1) with
    | none => simp [hk] at h
    | some r =>
      obtain ⟨ks₀, as₀⟩ := r
      simp only [hk] at h
      have iht := pushK_vars t n (extra + 1) ks₀ as₀ hk
      cases hg : ks₀[ks₀.length - extra - 1]? with
      | none => simp [hg] at h
      | some o =>
        cases o with
        | none =>
          simp only [hg, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          intro a ha
          simp [Term.vars, iht a ha]
        | some m =>
          simp only [hg] at h
          cases hu : pushK S u m 0 with
          | none => simp [hu] at h
          | some r' =>
            obtain ⟨ks₁, bs⟩ := r'
            simp only [hu, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            intro a ha
            rcases List.mem_append.1 ha with ha | ha
            · simp [Term.vars, iht a ha]
            · simp [Term.vars, pushK_vars u m 0 ks₁ bs hu a ha]

theorem push_vars {n : Name} {p : Pat} {as : Atoms} (h : push S n p = some as) :
    ∀ a ∈ as, a.1 ∈ p.vars := by
  unfold push at h
  cases hk : pushK S p n 0 with
  | none => simp [hk] at h
  | some r =>
    obtain ⟨ks, as'⟩ := r
    simp only [hk, Option.map_some, Option.some.injEq] at h
    subst h
    exact pushK_vars p n 0 ks as' hk

/-- The declared sorts that hold of every instance of a subterm with its
variables in their sorts: the ones that push down to sorts the variables
have. -/
def clo (S : Sorts) (r : Raw) (u : Pat) : Conj :=
  (names S).filter fun n =>
    (match push S n u with
    | some as => as.all fun a => decide (a.2 ∈ r.conj a.1)
    | none => false) = true

theorem mem_clo {r : Raw} {u : Pat} {n : Name} :
    n ∈ clo S r u ↔ n ∈ names S ∧ ∃ as, push S n u = some as ∧ ∀ a ∈ as, a.2 ∈ r.conj a.1 := by
  unfold clo
  rw [Finset.mem_filter]
  cases hp : push S n u with
  | none => simp
  | some as => simp

/-- A sort of a subterm holds of its instances. -/
theorem clo_mem {r : Raw} {u : Pat} (hfo : u.firstOrder = true) {n : Name} (hn : n ∈ clo S r u)
    {σ : Nat → GTerm} (hσ : σ ∈ r.store.Pos S) : mem S n (u.bind σ) = true := by
  obtain ⟨-, as, hp, hall⟩ := mem_clo.1 hn
  exact (push_some hfo hp σ).2 fun a ha => hσ a.1 a.2 (hall a ha)

/-- A sort that holds of the instance of a subterm at every solution is a
sort of the subterm. -/
theorem mem_clo_of_all {r : Raw} (hr : r.Shaped S) {u : Pat} (hfo : u.firstOrder = true)
    (huv : ∀ y ∈ u.vars, y < r.c.length) {σ₀ : Nat → GTerm} (hσ₀ : σ₀ ∈ r.store.Sol S) {n : Name}
    (hall : ∀ σ ∈ r.store.Sol S, mem S n (u.bind σ) = true) : n ∈ clo S r u := by
  refine mem_clo.2 ⟨?_, ?_⟩
  · by_contra hn
    have := mem_false_of_not_names hn (u.bind σ₀)
    rw [hall σ₀ hσ₀] at this
    cases this
  · cases hp : push S n u with
    | none =>
      have := push_none hfo hp σ₀
      rw [hall σ₀ hσ₀] at this
      cases this
    | some as =>
      refine ⟨as, rfl, fun a ha => ?_⟩
      have hm : ∀ σ ∈ r.store.Sol S, mem S a.2 (σ a.1) = true :=
        fun σ hσ => (push_some hfo hp σ).1 (hall σ hσ) a ha
      refine (hr.up a.1 (huv _ (push_vars hp a ha)) a.2).2 ⟨?_, hm⟩
      by_contra hn'
      have := mem_false_of_not_names hn' (σ₀ a.1)
      rw [hm σ₀ hσ₀] at this
      cases this

/-- A member of the sorts of a free subterm is its instance at a solution. -/
theorem Free.inst {r : Raw} (hr : r.Shaped S) {u : Pat} (hfo : u.firstOrder = true)
    (huv : ∀ y ∈ u.vars, y < r.c.length) (hf : Free S r.store u) {σ₀ : Nat → GTerm}
    (hσ₀ : σ₀ ∈ r.store.Sol S) {g : GTerm} (hg : MemC S (clo S r u) g) :
    ∃ σ ∈ r.store.Sol S, u.bind σ = g := by
  obtain ⟨C, hC₁, hC₂⟩ := hf.sem
  have hCg : MemC S C g := fun n hn =>
    hg n (mem_clo_of_all hr hfo huv hσ₀ fun σ hσ => hC₁ σ hσ n hn)
  obtain ⟨σ', hσ', e, -⟩ := hC₂ σ₀ hσ₀ g hCg
  exact ⟨σ', hσ', e⟩

/-! ## Free, decided -/

/-- A solution changed on variables no exclusion mentions, to values of
their sorts, is a solution. -/
theorem sol_vary {r : Raw} {σ σ' : Nat → GTerm} (hσ : σ ∈ r.store.Sol S) {V : List Nat}
    (hout : ∀ y, y ∉ V → σ' y = σ y) (hin : ∀ y ∈ V, MemC S (r.conj y) (σ' y))
    (hx : ∀ θ ∈ r.x, ∀ y ∈ V, y ∉ (eqnsOf θ).vars) : σ' ∈ r.store.Sol S := by
  refine ⟨fun y => ?_, fun E hE hu => ?_⟩
  · by_cases hy : y ∈ V
    · exact hin y hy
    · rw [hout y hy]
      exact hσ.1 y
  · obtain ⟨θ, hθ, rfl⟩ := Raw.mem_store_x.1 hE
    refine hσ.2 _ hE (unifies_congr (fun p hp v hv => hout v fun hV => ?_) hu)
    exact hx θ hθ v hV (List.mem_flatMap.2 ⟨p, hp, hv⟩)

/-- The term is not a variable. -/
def notVar : Pat → Bool
  | .var _ => false
  | _ => true

theorem notVar_iff {u : Pat} : notVar u = true ↔ ∀ x, u ≠ .var x := by
  cases u <;> simp [notVar]

/-- Whether a subterm of a store is free, decided on the store: it is not a
variable, has a variable and none twice, its variables occur nowhere else in
the pattern and in no exclusion, and the members of its sorts are its
instances. -/
def freeB (S : Sorts) (r : Raw) (u : Pat) : Bool :=
  notVar u && decide (u.vars ≠ []) && decide u.vars.Nodup &&
    decide (∀ y ∈ u.vars, y ∉ outV u r.t) &&
    decide (∀ θ ∈ r.x, ∀ y ∈ u.vars, y ∉ (eqnsOf θ).vars) &&
    fitsIn S r.conj (clo S r u) u

/-- `freeB` decides `Free`. -/
theorem freeB_iff (hS : S.WellFormed) {r : Raw} (hR : r.Roomy S) {u : Pat}
    (hfo : u.firstOrder = true) (huv : ∀ y ∈ u.vars, y < r.c.length) :
    freeB S r u = true ↔ Free S r.store u := by
  obtain ⟨σ₀, hσ₀⟩ := hR.sol
  have hr := hR.shaped
  have hw : MemC S (clo S r u) (u.bind σ₀) := fun n hn => clo_mem hfo hn hσ₀.1
  have hfit := fun hlin : u.vars.Nodup =>
    fitsIn_iff hS r.conj _ u rfl (clo S r u) hfo hlin σ₀ (fun y _ => hσ₀.1 y) hw
  constructor
  · intro h
    simp only [freeB, Bool.and_eq_true, decide_eq_true_iff, notVar_iff] at h
    obtain ⟨⟨⟨⟨⟨happ, hne⟩, hlin⟩, hin⟩, hx⟩, hfits⟩ := h
    refine ⟨happ, hne, hlin, hin, clo S r u, fun σ hσ n hn => clo_mem hfo hn hσ.1,
      fun σ hσ g hg => ?_⟩
    obtain ⟨σg, hσg, e⟩ := (hfit hlin).1 hfits g hg
    classical
    refine ⟨fun y => if y ∈ u.vars then σg y else σ y,
      sol_vary hσ (fun y hy => by simp [hy]) (fun y hy => by simpa [hy] using hσg y hy) hx,
      ?_, fun y _ hy => by simp [hy]⟩
    rw [← e]
    exact Term.bind_congr fun y hy => by simp [hy]
  · intro hf
    have hx := hf.not_excl hS hR hfo huv
    simp only [freeB, Bool.and_eq_true, decide_eq_true_iff, notVar_iff]
    refine ⟨⟨⟨⟨⟨hf.app, hf.ne⟩, hf.lin⟩, hf.inside⟩, hx⟩, ?_⟩
    refine (hfit hf.lin).2 fun h hh => ?_
    obtain ⟨σ', hσ', e⟩ := hf.inst hr hfo huv hσ₀ hh
    exact ⟨σ', fun y _ => hσ'.1 y, e⟩

end Sorts
end RwLog
