/-
# The derivations of an expression

`paths neg e` lists every derivation of `e` (of its converse with `neg`) in
the normalizer's order: one branch of every choice, with its key.

* The normal form of `e` is the normal forms of its derivations, one after
  the other (`norm_paths`), and a derivation has at most one product
  (`norm_path_le`).
* The keys of the derivations are in strictly increasing order
  (`paths_before`).

`WR neg e R` lists the derivations the walk from the right hands on, in the
walk's order (`walkR_val`). They are derivations of `e` (`mem_paths_of_WR`),
each once (`nodup_WR`).
-/
import RwLog.Rungs.R004.Spec
import RwLog.Rungs.R000.Products
import RwLog.Rungs.R000.Unfold
import RwLog.Rungs.Framework.Cost
import RwLog.Lib.Insert

namespace RwLog

namespace R004

open R000 Cost

/-! ## Building derivations -/

namespace Path

def inl (x : Path) : Path := ⟨.inl x.key, x.pe⟩
def inr (x : Path) : Path := ⟨.inr x.key, x.pe⟩
def seq (p q : Path) : Path := ⟨.pair p.key q.key, .seq p.pe q.pe⟩
def and (p q : Path) : Path := ⟨.pair p.key q.key, .and p.pe q.pe⟩

theorem inl_inj {x y : Path} (h : x.inl = y.inl) : x = y := by
  cases x; cases y; simp only [inl, Path.mk.injEq, Key.inl.injEq] at h; simp [h]

theorem inr_inj {x y : Path} (h : x.inr = y.inr) : x = y := by
  cases x; cases y; simp only [inr, Path.mk.injEq, Key.inr.injEq] at h; simp [h]

theorem inl_ne_inr (x y : Path) : x.inl ≠ y.inr := by
  intro h; simp [inl, inr] at h

theorem seq_inj {p q p' q' : Path} (h : p.seq q = p'.seq q') : p = p' ∧ q = q' := by
  cases p; cases q; cases p'; cases q'
  simp only [seq, Path.mk.injEq, Key.pair.injEq, RelOf.seq.injEq] at h
  simp [h]

theorem and_inj {p q p' q' : Path} (h : p.and q = p'.and q') : p = p' ∧ q = q' := by
  cases p; cases q; cases p'; cases q'
  simp only [and, Path.mk.injEq, Key.pair.injEq, RelOf.and.injEq] at h
  simp [h]

end Path

/-- Every derivation of `e` (of its converse with `neg`), in the normalizer's
order. -/
def paths : Bool → Rel → List Path
  | _, .zero => []
  | neg, .span s => [⟨.leaf, .span (if neg then s.swap else s)⟩]
  | neg, .or a b => (paths neg a).map Path.inl ++ (paths neg b).map Path.inr
  | false, .seq a b => (paths false a).flatMap fun p => (paths false b).map fun q => p.seq q
  | true, .seq a b => (paths true b).flatMap fun p => (paths true a).map fun q => p.seq q
  | neg, .and a b => (paths neg a).flatMap fun p => (paths neg b).map fun q => p.and q
  | neg, .conv a => paths (!neg) a
  | neg, .call n => [⟨.leaf, if neg then .conv (.call n) else .call n⟩]

/-! ## The normal form, derivation by derivation -/

theorem flatMap_comm_of_le_one {α β γ : Type} {l : List α} (h : l.length ≤ 1) (m : List β)
    (F : α → β → List γ) :
    (l.flatMap fun p => m.flatMap (F p)) = m.flatMap fun y => l.flatMap fun p => F p y := by
  match l, h with
  | [], _ => simp
  | [p], _ => simp

theorem length_flatMap_le_one {α β : Type} {l : List α} (h : l.length ≤ 1) (f : α → List β)
    (hf : ∀ x ∈ l, (f x).length ≤ 1) : (l.flatMap f).length ≤ 1 := by
  match l, h with
  | [], _ => simp
  | [p], _ => simpa using hf p (by simp)

theorem length_filterMap_le_one {α β : Type} {l : List α} (h : l.length ≤ 1) (f : α → Option β) :
    (l.filterMap f).length ≤ 1 :=
  Nat.le_trans (List.length_filterMap_le f l) h

/-- A derivation has at most one product. -/
theorem norm_path_le : ∀ (e : Rel) (neg : Bool), ∀ x ∈ paths neg e,
    (norm false x.pe).length ≤ 1 := by
  intro e
  induction e with
  | zero => intro neg x hx; simp [paths] at hx
  | span s =>
    intro neg x hx
    simp only [paths, List.mem_singleton] at hx
    subst hx
    simp [norm]
  | or a b iha ihb =>
    intro neg x hx
    simp only [paths, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · exact iha neg y hy
    · exact ihb neg y hy
  | seq a b iha ihb =>
    intro neg x hx
    have key : ∀ p q : Path, (norm false p.pe).length ≤ 1 → (norm false q.pe).length ≤ 1 →
        (norm false (p.seq q).pe).length ≤ 1 := fun p q hp hq =>
      length_flatMap_le_one hp _ fun _ _ => length_filterMap_le_one hq _
    cases neg
    · simp only [paths, List.mem_flatMap, List.mem_map] at hx
      obtain ⟨p, hp, q, hq, rfl⟩ := hx
      exact key p q (iha false p hp) (ihb false q hq)
    · simp only [paths, List.mem_flatMap, List.mem_map] at hx
      obtain ⟨p, hp, q, hq, rfl⟩ := hx
      exact key p q (ihb true p hp) (iha true q hq)
  | and a b iha ihb =>
    intro neg x hx
    simp only [paths, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨p, hp, q, hq, rfl⟩ := hx
    exact length_flatMap_le_one (iha neg p hp) _ fun _ _ =>
      length_filterMap_le_one (ihb neg q hq) _
  | conv a iha => intro neg x hx; exact iha (!neg) x hx
  | call n =>
    intro neg x hx
    simp only [paths, List.mem_singleton] at hx
    subst hx
    cases neg <;> simp [norm]

/-- The normal form of a product of two expressions, from the normal forms of
the derivations of each. -/
theorem prod_paths {A B : List Path} (J : List Rel → List Rel → Option (List Rel))
    (hA : ∀ x ∈ A, (norm false x.pe).length ≤ 1) :
    ((A.flatMap fun x => norm false x.pe).flatMap fun p =>
        (B.flatMap fun y => norm false y.pe).filterMap (J p)) =
      (A.flatMap fun x => B.flatMap fun y =>
        (norm false x.pe).flatMap fun p => (norm false y.pe).filterMap (J p)) := by
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun x hx => ?_
  simp only [List.filterMap_flatMap]
  exact flatMap_comm_of_le_one (hA x hx) B _

/-- The normal form of an expression is the normal forms of its derivations,
one after the other. -/
theorem norm_paths : ∀ (e : Rel) (neg : Bool),
    norm neg e = (paths neg e).flatMap fun x => norm false x.pe := by
  intro e
  induction e with
  | zero => intro neg; simp [paths, norm]
  | span s => intro neg; simp [paths, norm]
  | or a b iha ihb =>
    intro neg
    simp only [paths, norm, List.flatMap_append, List.flatMap_map, Path.inl, Path.inr]
    rw [iha neg, ihb neg]
  | seq a b iha ihb =>
    intro neg
    cases neg
    · simp only [paths, norm, List.flatMap_assoc, List.flatMap_map, Path.seq]
      rw [iha false, ihb false, prod_paths _ (norm_path_le a false)]
    · simp only [paths, norm, List.flatMap_assoc, List.flatMap_map, Path.seq]
      rw [iha true, ihb true, prod_paths _ (norm_path_le b true)]
  | and a b iha ihb =>
    intro neg
    simp only [paths, norm, List.flatMap_assoc, List.flatMap_map, Path.and]
    rw [iha neg, ihb neg, prod_paths _ (norm_path_le a neg)]
  | conv a iha => intro neg; simp only [paths, norm]; exact iha (!neg)
  | call n => intro neg; cases neg <;> simp [paths, norm]

/-! ## The order of the keys -/

theorem Key.lt_irrefl : ∀ k : Key, Key.lt k k = false
  | .leaf => rfl
  | .inl a => by simp [Key.lt, Key.lt_irrefl a]
  | .inr a => by simp [Key.lt, Key.lt_irrefl a]
  | .pair a b => by simp [Key.lt, Key.lt_irrefl a, Key.lt_irrefl b]

/-- `x` is listed before `y`: its key is smaller. -/
def KeyBefore (x y : Path) : Prop := Before Key.lt x.key y.key

theorem keyBefore_pair_left {p p' : Path} (h : KeyBefore p p') (k k' : Key) :
    Before Key.lt (.pair p.key k) (.pair p'.key k') := by
  obtain ⟨h1, h2⟩ := h
  have hne : p'.key ≠ p.key := fun e => by
    rw [e, Key.lt_irrefl] at h1; exact Bool.noConfusion h1
  exact ⟨by simp [Key.lt, h1], by simp [Key.lt, h2, hne]⟩

theorem keyBefore_pair_right (k : Key) {q q' : Path} (h : KeyBefore q q') :
    Before Key.lt (.pair k q.key) (.pair k q'.key) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by simp [Key.lt, h1], by simp [Key.lt, h2, Key.lt_irrefl]⟩

theorem pairwise_prod {A B : List Path} (f : Path → Path → Path)
    (hk : ∀ p q, (f p q).key = .pair p.key q.key)
    (hA : A.Pairwise KeyBefore) (hB : B.Pairwise KeyBefore) :
    (A.flatMap fun p => B.map fun q => f p q).Pairwise KeyBefore := by
  rw [List.pairwise_flatMap]
  refine ⟨fun p _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact hB.imp fun {q q'} h => by
      show Before Key.lt (f p q).key (f p q').key
      rw [hk, hk]
      exact keyBefore_pair_right _ h
  · exact hA.imp fun {p p'} h x hx y hy => by
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨q', _, rfl⟩ := List.mem_map.mp hy
      show Before Key.lt (f p q).key (f p' q').key
      rw [hk, hk]
      exact keyBefore_pair_left h _ _

/-- The derivations are listed in the order of their keys. -/
theorem paths_before : ∀ (e : Rel) (neg : Bool), (paths neg e).Pairwise KeyBefore := by
  intro e
  induction e with
  | zero => intro neg; simp [paths]
  | span s => intro neg; simp [paths]
  | or a b iha ihb =>
    intro neg
    simp only [paths]
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact (iha neg).imp fun {x y} h => by
        obtain ⟨h1, h2⟩ := h
        exact ⟨by simpa [Path.inl, Key.lt] using h1, by simpa [Path.inl, Key.lt] using h2⟩
    · rw [List.pairwise_map]
      exact (ihb neg).imp fun {x y} h => by
        obtain ⟨h1, h2⟩ := h
        exact ⟨by simpa [Path.inr, Key.lt] using h1, by simpa [Path.inr, Key.lt] using h2⟩
    · intro x hx y hy
      obtain ⟨x', _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨y', _, rfl⟩ := List.mem_map.mp hy
      exact ⟨by simp [Path.inl, Path.inr, Key.lt], by simp [Path.inl, Path.inr, Key.lt]⟩
  | seq a b iha ihb =>
    intro neg
    cases neg
    · exact pairwise_prod Path.seq (fun _ _ => rfl) (iha false) (ihb false)
    · exact pairwise_prod Path.seq (fun _ _ => rfl) (ihb true) (iha true)
  | and a b iha ihb =>
    intro neg
    exact pairwise_prod Path.and (fun _ _ => rfl) (iha neg) (ihb neg)
  | conv a iha => intro neg; exact iha (!neg)
  | call n => intro neg; simp [paths]

/-! ## What the walk from the right hands on -/

/-- The derivations of `e` that can be followed by the chain `R`, in the order
of the walk from the right. -/
def WR : Bool → Rel → List Span → List Path
  | _, .zero, _ => []
  | neg, .span s, R =>
    if (fits (if neg then s.swap else s) R).val then [⟨.leaf, .span (if neg then s.swap else s)⟩]
    else []
  | neg, .or a b, R => (WR neg a R).map Path.inl ++ (WR neg b R).map Path.inr
  | false, .seq a b, R =>
    (WR false b R).flatMap fun q => (WR false a (front q.pe R)).map fun p => p.seq q
  | true, .seq a b, R =>
    (WR true a R).flatMap fun q => (WR true b (front q.pe R)).map fun p => p.seq q
  | neg, .and a b, _ => (WR neg a []).flatMap fun x => (WR neg b []).map fun y => x.and y
  | neg, .conv a, R => WR (!neg) a R
  | neg, .call n, _ => [⟨.leaf, if neg then .conv (.call n) else .call n⟩]

/-- Every derivation the walk hands on is a derivation. -/
theorem mem_paths_of_WR : ∀ (e : Rel) (neg : Bool) (R : List Span), ∀ x ∈ WR neg e R,
    x ∈ paths neg e := by
  intro e
  induction e with
  | zero => intro neg R x hx; simp [WR] at hx
  | span s =>
    intro neg R x hx
    simp only [WR] at hx
    simp only [paths, List.mem_singleton]
    by_cases h : (fits (if neg = true then s.swap else s) R).val = true
    · simpa [h] using hx
    · simp [h] at hx
  | or a b iha ihb =>
    intro neg R x hx
    simp only [WR, List.mem_append, List.mem_map] at hx
    simp only [paths, List.mem_append, List.mem_map]
    rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · exact .inl ⟨y, iha neg R y hy, rfl⟩
    · exact .inr ⟨y, ihb neg R y hy, rfl⟩
  | seq a b iha ihb =>
    intro neg R x hx
    cases neg
    · simp only [WR, List.mem_flatMap, List.mem_map] at hx
      obtain ⟨q, hq, p, hp, rfl⟩ := hx
      simp only [paths, List.mem_flatMap, List.mem_map]
      exact ⟨p, iha false _ p hp, q, ihb false R q hq, rfl⟩
    · simp only [WR, List.mem_flatMap, List.mem_map] at hx
      obtain ⟨q, hq, p, hp, rfl⟩ := hx
      simp only [paths, List.mem_flatMap, List.mem_map]
      exact ⟨p, ihb true _ p hp, q, iha true R q hq, rfl⟩
  | and a b iha ihb =>
    intro neg R x hx
    simp only [WR, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨p, hp, q, hq, rfl⟩ := hx
    simp only [paths, List.mem_flatMap, List.mem_map]
    exact ⟨p, iha neg [] p hp, q, ihb neg [] q hq, rfl⟩
  | conv a iha => intro neg R x hx; exact iha (!neg) R x hx
  | call n => intro neg R x hx; simpa [WR, paths] using hx

theorem nodup_prod {A : List Path} {B : Path → List Path} (f : Path → Path → Path)
    (hf : ∀ {p q p' q'}, f p q = f p' q' → p = p' ∧ q = q')
    (hA : A.Nodup) (hB : ∀ p ∈ A, (B p).Nodup) :
    (A.flatMap fun p => (B p).map fun q => f p q).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun p hp => (hB p hp).map fun q q' h => (hf h).2, ?_⟩
  exact hA.imp fun {p p'} hne => by
    rw [Function.onFun, List.disjoint_left]
    intro x hx hy
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨q', _, e⟩ := List.mem_map.mp hy
    exact hne (hf e).1.symm

/-- The walk hands each derivation on once. -/
theorem nodup_WR : ∀ (e : Rel) (neg : Bool) (R : List Span), (WR neg e R).Nodup := by
  intro e
  induction e with
  | zero => intro neg R; simp [WR]
  | span s =>
    intro neg R
    rw [WR]
    by_cases h : (fits (if neg = true then s.swap else s) R).val = true <;> simp [h]
  | or a b iha ihb =>
    intro neg R
    simp only [WR]
    rw [List.nodup_append]
    refine ⟨(iha neg R).map fun _ _ h => Path.inl_inj h, (ihb neg R).map fun _ _ h => Path.inr_inj h,
      ?_⟩
    intro x hx y hy
    obtain ⟨x', _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨y', _, rfl⟩ := List.mem_map.mp hy
    exact Path.inl_ne_inr x' y'
  | seq a b iha ihb =>
    intro neg R
    cases neg
    · exact nodup_prod (fun q p => p.seq q) (fun h => (Path.seq_inj h).symm) (ihb false R)
        fun q _ => iha false _
    · exact nodup_prod (fun q p => p.seq q) (fun h => (Path.seq_inj h).symm) (iha true R)
        fun q _ => ihb true _
  | and a b iha ihb =>
    intro neg R
    exact nodup_prod Path.and Path.and_inj (iha neg []) fun _ _ => ihb neg []
  | conv a iha => intro neg R; exact iha (!neg) R
  | call n => intro neg R; simp [WR]

/-! ## The walk -/

/-- Hand the derivations to `k` in order, threading what it has collected,
until it says stop. -/
def run {α : Type} (k : Path → α → Cost (Bool × α)) : List Path → α → Bool × α
  | [], acc => (false, acc)
  | p :: ps, acc => if (k p acc).val.1 then (k p acc).val else run k ps (k p acc).val.2

variable {α : Type}

theorem run_singleton (k : Path → α → Cost (Bool × α)) (p : Path) (acc : α) :
    run k [p] acc = (k p acc).val := by
  simp only [run]
  split
  · rfl
  · rename_i h
    have h' : (k p acc).val.1 = false := by simpa using h
    exact Prod.ext h'.symm rfl

theorem run_append (k : Path → α → Cost (Bool × α)) (xs ys : List Path) (acc : α) :
    run k (xs ++ ys) acc =
      if (run k xs acc).1 then run k xs acc else run k ys (run k xs acc).2 := by
  induction xs generalizing acc with
  | nil => simp [run]
  | cons p xs ih =>
    simp only [List.cons_append, run]
    split
    · simp
    · exact ih _

theorem run_flatMap (k k' : Path → α → Cost (Bool × α)) (F : Path → List Path) (xs : List Path)
    (h : ∀ p acc, (k' p acc).val = run k (F p) acc) (acc : α) :
    run k' xs acc = run k (xs.flatMap F) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons p xs ih =>
    rw [List.flatMap_cons, run_append]
    simp only [run, h, ih]

theorem run_map (k : Path → α → Cost (Bool × α)) (f : Path → Path) (xs : List Path) (acc : α) :
    run (fun x acc => k (f x) acc) xs acc = run k (xs.map f) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons p xs ih => simp only [List.map_cons, run, ih]

/-- The invariant at one depth, given it for the calls at that depth. -/
theorem walkR_step (P : Program) (d : Nat)
    (hcall : ∀ n neg R (k : Path → α → Cost (Bool × α)) acc,
      (walkR P d neg (.call n) R k acc).val = run k (WR neg (unfoldN P d (.call n)) R) acc) :
    ∀ e neg R (k : Path → α → Cost (Bool × α)) acc,
      (walkR P d neg e R k acc).val = run k (WR neg (unfoldN P d e) R) acc := by
  intro e
  induction e with
  | zero =>
    intro neg R k acc
    rw [unfoldN_zero, walkR]
    rfl
  | span s =>
    intro neg R k acc
    rw [unfoldN_span, walkR]
    simp only [bind_val, WR]
    by_cases h : (fits (if neg = true then s.swap else s) R).val = true
    · simp only [h, ↓reduceIte]
      exact (run_singleton k _ acc).symm
    · simp only [h]
      rfl
  | or a b iha ihb =>
    intro neg R k acc
    rw [unfoldN_or, walkR, WR, run_append, ← run_map, ← run_map, ← iha, ← ihb]
    simp only [bind_val, ite_val, pure_val]
    rfl
  | seq a b iha ihb =>
    intro neg R k acc
    rw [unfoldN_seq]
    cases neg
    · rw [walkR, WR]
      simp only [bind_val]
      rw [ihb]
      refine run_flatMap k _ _ _ (fun q acc => ?_) acc
      rw [iha]
      exact run_map k (fun p => p.seq q) _ acc
    · rw [walkR, WR]
      simp only [bind_val]
      rw [iha]
      refine run_flatMap k _ _ _ (fun q acc => ?_) acc
      rw [ihb]
      exact run_map k (fun p => p.seq q) _ acc
  | and a b iha ihb =>
    intro neg R k acc
    rw [unfoldN_and, walkR, WR]
    simp only [bind_val]
    rw [iha]
    refine run_flatMap k _ _ _ (fun x acc => ?_) acc
    rw [ihb]
    exact run_map k (fun y => x.and y) _ acc
  | conv a iha =>
    intro neg R k acc
    rw [unfoldN_conv, walkR, WR, ← iha]
    rfl
  | call n => exact hcall n

/-- The walk from the right hands the continuation exactly the derivations of
`WR`, in order. -/
theorem walkR_val (P : Program) : ∀ (d : Nat) (e : Rel) (neg : Bool) (R : List Span)
    (k : Path → α → Cost (Bool × α)) (acc : α),
    (walkR P d neg e R k acc).val = run k (WR neg (unfoldN P d e) R) acc := by
  intro d
  induction d with
  | zero =>
    refine walkR_step P 0 fun n neg R k acc => ?_
    rw [walkR]
    exact (run_singleton k _ acc).symm
  | succ d ih =>
    refine walkR_step P (d + 1) fun n neg R k acc => ?_
    rw [walkR]
    exact ih (P.body n) neg R k acc

end R004

end RwLog
