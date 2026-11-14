/-
# A split and its image

The candidates and the strategies of a split of a chain or a meet
(`Tabled.way`), in two runs of the tabled machine that correspond
(`Rungs/Tabled/MapGoal.lean`).

The image of a split keeps its two sides in order, or exchanges them:

* a split of a meet and its image side by side (`way_and_cand`,
  `way_and_strat`), and a split of a chain when the node map is not the
  converse (`way_seq_cand`, `way_seq_strat`);
* a split of a chain under the converse, where the image of the left side is
  the right side: joining becomes joining the other way round and pushing
  left becomes pushing right (`way_conv_cand`, `way_conv_strat`);
* a split of a meet with its sides exchanged, in one run (`way_swap_cand`,
  `way_swap_strat`): the meet of two members is split at its first member,
  and the first member of the image need not be the image of the first.
-/
import RwLog.Rungs.Tabled.MapGoal

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P P' : Program}

/-- One list of goals is the image of another, as a set. -/
def Img (f : GoalOf R Rel → GoalOf R Rel) (s s' : List (GoalOf R Rel)) : Prop :=
  (∀ d ∈ s, f d ∈ s') ∧ ∀ d' ∈ s', ∃ d ∈ s, d' = f d

omit [DecidableEq R] in
theorem map_smap_false (o : Option R) : o.map (smap false) = o := by cases o <;> rfl

variable (K : Kernel R Cost) (hK : K.Refines D)

/-- A join carried to two other answers. -/
theorem join_tr {f : R → R} {x y c : Ans D P} {p q : Ans D P'}
    (hc : (Ans.join D P K hK x y).val = some c)
    (hop : D.compose p.span q.span = (D.compose x.span y.span).map f)
    (hok : JoinOk D p.span p.goal.rb q.goal.lb q.span) :
    ∃ c', (Ans.join D P' K hK p q).val = some c' ∧ c'.span = f c.span := by
  rw [((Ans.join_val K hK).1 hc).2.1] at hop
  obtain ⟨c', h, e, -⟩ := Ans.join_ok K hK hok hop
  exact ⟨c', h, e⟩

/-- A meet carried to two other answers. -/
theorem meet_tr {f : R → R} {x y c : Ans D P} {p q : Ans D P'}
    (hc : (Ans.meetA D P K hK x y).val = some c)
    (hop : D.meet p.span q.span = (D.meet x.span y.span).map f)
    (hok : MeetOk D p.span p.goal.lb p.goal.rb q.goal.lb q.goal.rb) :
    ∃ c', (Ans.meetA D P' K hK p q).val = some c' ∧ c'.span = f c.span := by
  rw [((Ans.meetA_val K hK).1 hc).2.1] at hop
  obtain ⟨c', h, e, -⟩ := Ans.meetA_ok K hK hok hop
  exact ⟨c', h, e⟩

section tied

variable {b t : Bool} {U : GOracle R Rel (Ans D P) Cost} {U' : GOracle R Rel (Ans D P') Cost}
  {ts : List (TableOf R Rel (Ans D P))} {ts' : List (TableOf R Rel (Ans D P'))}

/-- A maximal answer of the image of a goal is the image of a maximal answer
of the goal. -/
theorem maxima_back (hW : Twin D P P' b t U U') (hT : Tied b t ts ts') {g : GoalOf R Rel}
    (hg : Normal g.node) {x' : Ans D P'}
    (hx : x' ∈ (ansOf ts' (gmap b t g)).maximaBy (covB D P')) :
    ∃ x ∈ (ansOf ts g).maximaBy (covB D P), x'.span = smap b x.span := by
  obtain ⟨x, hx, e⟩ := maxima_fwd hW.symm hT.symm (normal_nmap b t g.node) hx
  rw [gmap_gmap hg] at hx
  exact ⟨x, hx, by rw [e, smap_smap hW.law']⟩

/-! ## A meet, side by side -/

section and

variable (hW : Twin D P P' b t U U') (hT : Tied b t ts ts') {g L Rg : GoalOf R Rel}
  (hLn : Normal L.node) (hRn : Normal Rg.node)
include hW hT hLn hRn

omit [DecidableEq R] hT hLn hRn in
theorem meet_smap (x y : R) :
    D.meet (smap b x) (smap b y) = (D.meet x y).map (smap b) := by
  cases b
  · exact (map_smap_false _).symm
  · exact hW.law.meet_swap x y

omit [DecidableEq R] hT hLn hRn in
theorem pushLG_and {x : Ans D P} {x' : Ans D P'} (e : x'.span = smap b x.span) :
    pushLG D (gmap b t g) (gmap b t Rg) .and x' = gmap b t (pushLG D g Rg .and x) := by
  cases b
  · show (⟨D.leftBound x'.span, _, D.rightBound x'.span⟩ : GoalOf R Rel) = _
    rw [e]; rfl
  · show (⟨D.leftBound x'.span, _, D.rightBound x'.span⟩ : GoalOf R Rel) =
      ⟨D.rightBound x.span, _, D.leftBound x.span⟩
    rw [e]
    show (⟨D.leftBound (swap x.span), _, D.rightBound (swap x.span)⟩ : GoalOf R Rel) = _
    rw [leftBound_swap hW.law]; rfl

omit [DecidableEq R] hT hLn hRn in
theorem pushRG_and {y : Ans D P} {y' : Ans D P'} (e : y'.span = smap b y.span) :
    pushRG D (gmap b t g) (gmap b t L) .and y' = gmap b t (pushRG D g L .and y) :=
  pushLG_and (g := g) (Rg := L) hW e

theorem way_and_cand (h₁ : Rg.lb = L.lb) (h₂ : Rg.rb = L.rb) {c : Ans D P}
    (hc : c ∈ (way (K := DerivationKernel.over D K hK P) ts g (.and, L, Rg)).val.1) :
    ∃ c' ∈ (way (K := DerivationKernel.over D K hK P') ts' (gmap b t g)
        (.and, gmap b t L, gmap b t Rg)).val.1, c'.span = smap b c.span := by
  have hlb : (gmap b t Rg).lb = (gmap b t L).lb := by cases b <;> simp [gmap, h₁, h₂]
  have hrb : (gmap b t Rg).rb = (gmap b t L).rb := by cases b <;> simp [gmap, h₁, h₂]
  rcases (mem_way K hK ts g _ c).1 hc with
    ⟨x, hx, y, hy, hxy⟩ | ⟨hd, x, hx, y, hy, hxy⟩ | ⟨hd, y, hy, x, hx, hxy⟩
  · obtain ⟨x', hx', ex⟩ := hT.fwd.ans _ x hx
    obtain ⟨y', hy', ey⟩ := hT.fwd.ans _ y hy
    have gx := ansOf_goal hT.inv'.ok hx'
    have gy := ansOf_goal hT.inv'.ok hy'
    obtain ⟨c', hc', e⟩ := meet_tr K hK (f := smap b) (p := x') (q := y') hxy (by rw [ex, ey]; exact meet_smap hW _ _)
      (.inl ⟨by rw [gx, gy]; exact hlb, by rw [gx, gy]; exact hrb⟩)
    exact ⟨c', (mem_way K hK ts' _ _ c').2 (.inl ⟨x', hx', y', hy', hc'⟩), e⟩
  · obtain ⟨x', hx', ex⟩ := maxima_fwd hW hT hLn hx
    obtain ⟨y', hy', ey⟩ := hT.fwd.ans _ y hy
    rw [← pushLG_and hW ex] at hy'
    have gy := ansOf_goal hT.inv'.ok hy'
    obtain ⟨c', hc', e⟩ := meet_tr K hK (f := smap b) (p := x') (q := y') hxy (by rw [ex, ey]; exact meet_smap hW _ _)
      (.inr ⟨by rw [gy]; rfl, by rw [gy]; rfl⟩)
    exact ⟨c', (mem_way K hK ts' _ _ c').2
      (.inr (.inl ⟨hT.fwd.done _ hd, x', hx', y', hy', hc'⟩)), e⟩
  · obtain ⟨y', hy', ey⟩ := maxima_fwd hW hT hRn hy
    obtain ⟨x', hx', ex⟩ := hT.fwd.ans _ x hx
    rw [← pushRG_and hW ey] at hx'
    have gx := ansOf_goal hT.inv'.ok hx'
    obtain ⟨c', hc', e⟩ := meet_tr K hK (f := smap b) (p := y') (q := x') hxy
      (by rw [ex, ey]; exact meet_smap hW _ _) (.inr ⟨by rw [gx]; rfl, by rw [gx]; rfl⟩)
    exact ⟨c', (mem_way K hK ts' _ _ c').2
      (.inr (.inr ⟨hT.fwd.done _ hd, y', hy', x', hx', hc'⟩)), e⟩

theorem way_and_strat {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (way (K := DerivationKernel.over D K hK P) ts g (.and, L, Rg)).val.2) :
    ∃ strat' ∈ (way (K := DerivationKernel.over D K hK P') ts' (gmap b t g)
        (.and, gmap b t L, gmap b t Rg)).val.2, Img (gmap b t) strat strat' := by
  rcases (mem_way_strats K hK ts g _ strat).1 hs with rfl | ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · refine ⟨_, (mem_way_strats K hK _ _ _ _).2 (.inl rfl), ?_, ?_⟩
    · intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      exact hd.imp (congrArg _) (congrArg _)
    · intro d' hd'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd' ⊢
      rcases hd' with rfl | rfl
      · exact ⟨L, .inl rfl, rfl⟩
      · exact ⟨Rg, .inr rfl, rfl⟩
  · refine ⟨_, (mem_way_strats K hK _ _ _ _).2 (.inr (.inl ⟨hT.fwd.done _ hd, rfl⟩)), ?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact List.mem_cons_self ..
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
        obtain ⟨x', hx', ex⟩ := maxima_fwd hW hT hLn hx
        exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨x', hx', pushLG_and hW ex⟩)
    · intro d' hd'
      rcases List.mem_cons.1 hd' with rfl | hd'
      · exact ⟨L, List.mem_cons_self .., rfl⟩
      · obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hd'
        obtain ⟨x, hx, ex⟩ := maxima_back hW hT hLn hx'
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩), pushLG_and hW ex⟩
  · refine ⟨_, (mem_way_strats K hK _ _ _ _).2 (.inr (.inr ⟨hT.fwd.done _ hd, rfl⟩)), ?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact List.mem_cons_self ..
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hd
        obtain ⟨y', hy', ey⟩ := maxima_fwd hW hT hRn hy
        exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨y', hy', pushRG_and hW ey⟩)
    · intro d' hd'
      rcases List.mem_cons.1 hd' with rfl | hd'
      · exact ⟨Rg, List.mem_cons_self .., rfl⟩
      · obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hd'
        obtain ⟨y, hy, ey⟩ := maxima_back hW hT hRn hy'
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨y, hy, rfl⟩), pushRG_and hW ey⟩

end and

/-! ## A chain, side by side -/

section seq

variable (hW : Twin D P P' false t U U') (hT : Tied false t ts ts') {g L Rg : GoalOf R Rel}
  (hLn : Normal L.node) (hRn : Normal Rg.node)
include hW hT hLn hRn

omit [DecidableEq R] hW hT hLn hRn in
theorem pushLG_seq {x : Ans D P} {x' : Ans D P'} (e : x'.span = smap false x.span) :
    pushLG D (gmap false t g) (gmap false t Rg) .seq x' = gmap false t (pushLG D g Rg .seq x) := by
  show (⟨D.rightBound x'.span, _, _⟩ : GoalOf R Rel) = _
  rw [e]; rfl

omit [DecidableEq R] hW hT hLn hRn in
theorem pushRG_seq {y : Ans D P} {y' : Ans D P'} (e : y'.span = smap false y.span) :
    pushRG D (gmap false t g) (gmap false t L) .seq y' = gmap false t (pushRG D g L .seq y) := by
  show (⟨_, _, D.leftBound y'.span⟩ : GoalOf R Rel) = _
  rw [e]; rfl

theorem way_seq_cand (h₁ : L.rb = none) (h₂ : Rg.lb = none) {c : Ans D P}
    (hc : c ∈ (way (K := DerivationKernel.over D K hK P) ts g (.seq, L, Rg)).val.1) :
    ∃ c' ∈ (way (K := DerivationKernel.over D K hK P') ts' (gmap false t g)
        (.seq, gmap false t L, gmap false t Rg)).val.1, c'.span = smap false c.span := by
  rcases (mem_way K hK ts g _ c).1 hc with
    ⟨x, hx, y, hy, hxy⟩ | ⟨hd, x, hx, y, hy, hxy⟩ | ⟨hd, y, hy, x, hx, hxy⟩
  · obtain ⟨x', hx', ex⟩ := hT.fwd.ans _ x hx
    obtain ⟨y', hy', ey⟩ := hT.fwd.ans _ y hy
    have gx := ansOf_goal hT.inv'.ok hx'
    have gy := ansOf_goal hT.inv'.ok hy'
    obtain ⟨c', hc', e⟩ := join_tr K hK (f := smap false) (p := x') (q := y') hxy
      (by rw [ex, ey]; exact (map_smap_false _).symm)
      (.inl ⟨by rw [gx]; exact h₁, .inl (by rw [gy]; exact h₂)⟩)
    exact ⟨c', (mem_way K hK ts' _ _ c').2 (.inl ⟨x', hx', y', hy', hc'⟩), e⟩
  · obtain ⟨x', hx', ex⟩ := maxima_fwd hW hT hLn hx
    obtain ⟨y', hy', ey⟩ := hT.fwd.ans _ y hy
    rw [← pushLG_seq ex] at hy'
    have gx := ansOf_goal hT.inv'.ok (List.mem_maximaBy hx')
    have gy := ansOf_goal hT.inv'.ok hy'
    obtain ⟨c', hc', e⟩ := join_tr K hK (f := smap false) (p := x') (q := y') hxy
      (by rw [ex, ey]; exact (map_smap_false _).symm)
      (.inl ⟨by rw [gx]; exact h₁, .inr (by rw [gy]; rfl)⟩)
    exact ⟨c', (mem_way K hK ts' _ _ c').2
      (.inr (.inl ⟨hT.fwd.done _ hd, x', hx', y', hy', hc'⟩)), e⟩
  · obtain ⟨y', hy', ey⟩ := maxima_fwd hW hT hRn hy
    obtain ⟨x', hx', ex⟩ := hT.fwd.ans _ x hx
    rw [← pushRG_seq ey] at hx'
    have gx := ansOf_goal hT.inv'.ok hx'
    have gy := ansOf_goal hT.inv'.ok (List.mem_maximaBy hy')
    obtain ⟨c', hc', e⟩ := join_tr K hK (f := smap false) (p := x') (q := y') hxy
      (by rw [ex, ey]; exact (map_smap_false _).symm)
      (.inr ⟨by rw [gy]; exact h₂, by rw [gx]; rfl⟩)
    exact ⟨c', (mem_way K hK ts' _ _ c').2
      (.inr (.inr ⟨hT.fwd.done _ hd, y', hy', x', hx', hc'⟩)), e⟩

theorem way_seq_strat {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (way (K := DerivationKernel.over D K hK P) ts g (.seq, L, Rg)).val.2) :
    ∃ strat' ∈ (way (K := DerivationKernel.over D K hK P') ts' (gmap false t g)
        (.seq, gmap false t L, gmap false t Rg)).val.2, Img (gmap false t) strat strat' := by
  rcases (mem_way_strats K hK ts g _ strat).1 hs with rfl | ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · refine ⟨_, (mem_way_strats K hK _ _ _ _).2 (.inl rfl), ?_, ?_⟩
    · intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      exact hd.imp (congrArg _) (congrArg _)
    · intro d' hd'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd' ⊢
      rcases hd' with rfl | rfl
      · exact ⟨L, .inl rfl, rfl⟩
      · exact ⟨Rg, .inr rfl, rfl⟩
  · refine ⟨_, (mem_way_strats K hK _ _ _ _).2 (.inr (.inl ⟨hT.fwd.done _ hd, rfl⟩)), ?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact List.mem_cons_self ..
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
        obtain ⟨x', hx', ex⟩ := maxima_fwd hW hT hLn hx
        exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨x', hx', pushLG_seq ex⟩)
    · intro d' hd'
      rcases List.mem_cons.1 hd' with rfl | hd'
      · exact ⟨L, List.mem_cons_self .., rfl⟩
      · obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hd'
        obtain ⟨x, hx, ex⟩ := maxima_back hW hT hLn hx'
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩), pushLG_seq ex⟩
  · refine ⟨_, (mem_way_strats K hK _ _ _ _).2 (.inr (.inr ⟨hT.fwd.done _ hd, rfl⟩)), ?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact List.mem_cons_self ..
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hd
        obtain ⟨y', hy', ey⟩ := maxima_fwd hW hT hRn hy
        exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨y', hy', pushRG_seq ey⟩)
    · intro d' hd'
      rcases List.mem_cons.1 hd' with rfl | hd'
      · exact ⟨Rg, List.mem_cons_self .., rfl⟩
      · obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hd'
        obtain ⟨y, hy, ey⟩ := maxima_back hW hT hRn hy'
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨y, hy, rfl⟩), pushRG_seq ey⟩

end seq

/-! ## A chain under the converse -/

section conv

variable (hW : Twin D P P' true t U U') (hT : Tied true t ts ts') {g L Rg : GoalOf R Rel}
  (hLn : Normal L.node) (hRn : Normal Rg.node)
include hW hT hLn hRn

omit [DecidableEq R] hT hLn hRn in
/-- The goal pushed left for an answer, under the converse: the goal pushed
right for its converse. -/
theorem pushRG_conv {x : Ans D P} {x' : Ans D P'} (e : x'.span = smap true x.span) :
    pushRG D (gmap true t g) (gmap true t Rg) .seq x' = gmap true t (pushLG D g Rg .seq x) := by
  show (⟨_, _, D.leftBound x'.span⟩ : GoalOf R Rel) = ⟨_, _, D.rightBound x.span⟩
  rw [e]
  show (⟨_, _, D.leftBound (swap x.span)⟩ : GoalOf R Rel) = _
  rw [leftBound_swap hW.law]; rfl

omit [DecidableEq R] hW hT hLn hRn in
theorem pushLG_conv {y : Ans D P} {y' : Ans D P'} (e : y'.span = smap true y.span) :
    pushLG D (gmap true t g) (gmap true t L) .seq y' = gmap true t (pushRG D g L .seq y) := by
  show (⟨D.rightBound y'.span, _, _⟩ : GoalOf R Rel) = ⟨D.leftBound y.span, _, _⟩
  rw [e]; rfl

theorem way_conv_cand (h₁ : L.rb = none) (h₂ : Rg.lb = none) {c : Ans D P}
    (hc : c ∈ (way (K := DerivationKernel.over D K hK P) ts g (.seq, L, Rg)).val.1) :
    ∃ c' ∈ (way (K := DerivationKernel.over D K hK P') ts' (gmap true t g)
        (.seq, gmap true t Rg, gmap true t L)).val.1, c'.span = smap true c.span := by
  rcases (mem_way K hK ts g _ c).1 hc with
    ⟨x, hx, y, hy, hxy⟩ | ⟨hd, x, hx, y, hy, hxy⟩ | ⟨hd, y, hy, x, hx, hxy⟩
  · obtain ⟨x', hx', ex⟩ := hT.fwd.ans _ x hx
    obtain ⟨y', hy', ey⟩ := hT.fwd.ans _ y hy
    have gx := ansOf_goal hT.inv'.ok hx'
    have gy := ansOf_goal hT.inv'.ok hy'
    obtain ⟨c', hc', e⟩ := join_tr K hK (f := smap true) (p := y') (q := x') hxy
      (by rw [ex, ey]; exact hW.law.compose_swap _ _)
      (.inl ⟨by rw [gy]; exact h₂, .inl (by rw [gx]; exact h₁)⟩)
    exact ⟨c', (mem_way K hK ts' _ _ c').2 (.inl ⟨y', hy', x', hx', hc'⟩), e⟩
  · obtain ⟨x', hx', ex⟩ := maxima_fwd hW hT hLn hx
    obtain ⟨y', hy', ey⟩ := hT.fwd.ans _ y hy
    rw [← pushRG_conv hW ex] at hy'
    have gx := ansOf_goal hT.inv'.ok (List.mem_maximaBy hx')
    have gy := ansOf_goal hT.inv'.ok hy'
    obtain ⟨c', hc', e⟩ := join_tr K hK (f := smap true) (p := y') (q := x') hxy
      (by rw [ex, ey]; exact hW.law.compose_swap _ _)
      (.inr ⟨by rw [gx]; exact h₁, by rw [gy]; rfl⟩)
    exact ⟨c', (mem_way K hK ts' _ _ c').2
      (.inr (.inr ⟨hT.fwd.done _ hd, x', hx', y', hy', hc'⟩)), e⟩
  · obtain ⟨y', hy', ey⟩ := maxima_fwd hW hT hRn hy
    obtain ⟨x', hx', ex⟩ := hT.fwd.ans _ x hx
    rw [← pushLG_conv ey] at hx'
    have gx := ansOf_goal hT.inv'.ok hx'
    have gy := ansOf_goal hT.inv'.ok (List.mem_maximaBy hy')
    obtain ⟨c', hc', e⟩ := join_tr K hK (f := smap true) (p := y') (q := x') hxy
      (by rw [ex, ey]; exact hW.law.compose_swap _ _)
      (.inl ⟨by rw [gy]; exact h₂, .inr (by rw [gx]; rfl)⟩)
    exact ⟨c', (mem_way K hK ts' _ _ c').2
      (.inr (.inl ⟨hT.fwd.done _ hd, y', hy', x', hx', hc'⟩)), e⟩

theorem way_conv_strat {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (way (K := DerivationKernel.over D K hK P) ts g (.seq, L, Rg)).val.2) :
    ∃ strat' ∈ (way (K := DerivationKernel.over D K hK P') ts' (gmap true t g)
        (.seq, gmap true t Rg, gmap true t L)).val.2, Img (gmap true t) strat strat' := by
  rcases (mem_way_strats K hK ts g _ strat).1 hs with rfl | ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · refine ⟨_, (mem_way_strats K hK _ _ _ _).2 (.inl rfl), ?_, ?_⟩
    · intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      exact hd.symm.imp (congrArg _) (congrArg _)
    · intro d' hd'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd' ⊢
      rcases hd' with rfl | rfl
      · exact ⟨Rg, .inr rfl, rfl⟩
      · exact ⟨L, .inl rfl, rfl⟩
  · refine ⟨_, (mem_way_strats K hK _ _ _ _).2 (.inr (.inr ⟨hT.fwd.done _ hd, rfl⟩)), ?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact List.mem_cons_self ..
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
        obtain ⟨x', hx', ex⟩ := maxima_fwd hW hT hLn hx
        exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨x', hx', pushRG_conv hW ex⟩)
    · intro d' hd'
      rcases List.mem_cons.1 hd' with rfl | hd'
      · exact ⟨L, List.mem_cons_self .., rfl⟩
      · obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hd'
        obtain ⟨x, hx, ex⟩ := maxima_back hW hT hLn hx'
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩), pushRG_conv hW ex⟩
  · refine ⟨_, (mem_way_strats K hK _ _ _ _).2 (.inr (.inl ⟨hT.fwd.done _ hd, rfl⟩)), ?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact List.mem_cons_self ..
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hd
        obtain ⟨y', hy', ey⟩ := maxima_fwd hW hT hRn hy
        exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨y', hy', pushLG_conv ey⟩)
    · intro d' hd'
      rcases List.mem_cons.1 hd' with rfl | hd'
      · exact ⟨Rg, List.mem_cons_self .., rfl⟩
      · obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hd'
        obtain ⟨y, hy, ey⟩ := maxima_back hW hT hRn hy'
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨y, hy, rfl⟩), pushLG_conv ey⟩

end conv

end tied

/-! ## A meet with its sides exchanged -/

section swap

variable (hL : D.Lawful P.sorts.interp) {ts : List (TableOf R Rel (Ans D P))}
  (hT : TablesOk D ts) {g L Rg : GoalOf R Rel}

include hL hT in
theorem way_swap_cand (h₁ : Rg.lb = L.lb) (h₂ : Rg.rb = L.rb) {c : Ans D P}
    (hc : c ∈ (way (K := DerivationKernel.over D K hK P) ts g (.and, L, Rg)).val.1) :
    ∃ c' ∈ (way (K := DerivationKernel.over D K hK P) ts g (.and, Rg, L)).val.1,
      c'.span = c.span := by
  rcases (mem_way K hK ts g _ c).1 hc with
    ⟨x, hx, y, hy, hxy⟩ | ⟨hd, x, hx, y, hy, hxy⟩ | ⟨hd, y, hy, x, hx, hxy⟩
  · have gx := ansOf_goal hT hx
    have gy := ansOf_goal hT hy
    obtain ⟨c', hc', e⟩ := meet_tr K hK (f := id) (p := y) (q := x) hxy
      (by rw [hL.meet_comm]; exact (map_smap_false _).symm)
      (.inl ⟨by rw [gx, gy]; exact h₁.symm, by rw [gx, gy]; exact h₂.symm⟩)
    exact ⟨c', (mem_way K hK ts _ _ c').2 (.inl ⟨y, hy, x, hx, hc'⟩), e⟩
  · exact ⟨c, (mem_way K hK ts _ _ c).2 (.inr (.inr ⟨hd, x, hx, y, hy, hxy⟩)), rfl⟩
  · exact ⟨c, (mem_way K hK ts _ _ c).2 (.inr (.inl ⟨hd, y, hy, x, hx, hxy⟩)), rfl⟩

theorem way_swap_strat {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (way (K := DerivationKernel.over D K hK P) ts g (.and, L, Rg)).val.2) :
    ∃ strat' ∈ (way (K := DerivationKernel.over D K hK P) ts g (.and, Rg, L)).val.2,
      ∀ d, d ∈ strat' ↔ d ∈ strat := by
  rcases (mem_way_strats K hK ts g _ strat).1 hs with rfl | ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · exact ⟨_, (mem_way_strats K hK _ _ _ _).2 (.inl rfl), fun d => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact or_comm⟩
  · exact ⟨_, (mem_way_strats K hK _ _ _ _).2 (.inr (.inr ⟨hd, rfl⟩)), fun d => Iff.rfl⟩
  · exact ⟨_, (mem_way_strats K hK _ _ _ _).2 (.inr (.inl ⟨hd, rfl⟩)), fun d => Iff.rfl⟩

end swap

end Tabled

end RwLog
