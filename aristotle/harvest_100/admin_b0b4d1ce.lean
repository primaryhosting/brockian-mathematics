import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

We set up two-party communication protocols as protocol trees, and prove the
`Ω(n)` lower bound for the randomized communication complexity of set
disjointness on `n`-element ground sets: any public-coin randomized protocol
which never wrongly claims that two intersecting sets are disjoint, and which
detects disjointness with probability at least `1/2`, must communicate at least
`n - 1` bits (`CS.disjointness_lb`).

The proof combines the classical fooling set `{(S, Sᶜ) : S ⊆ Fin n}` of size
`2 ^ n` for disjointness with an averaging argument over the public random
string.  We also record the matching upper bound `n + 1`
(`CS.disjointness_ub`), which shows in particular that the hypotheses of the
lower bound are satisfiable, and the deterministic lower bound `n`
(`CS.disjointness_deterministic_lb`).

The randomized bound proved here is for protocols with one-sided error (they
never certify disjointness wrongly); the two-sided bounded-error case is
Razborov's theorem and is not covered by this argument.
-/

open Finset

namespace CS

open scoped Classical

/-- A deterministic two-party communication protocol tree.  `alice g L R` means
"Alice sends the bit `g x` and the players continue with `L` (if the bit is
`true`) or `R` (if it is `false`)"; `bob` is the same with Bob speaking. -/
inductive Prot (X Y : Type*) : Type _
  | leaf : Bool → Prot X Y
  | alice : (X → Bool) → Prot X Y → Prot X Y → Prot X Y
  | bob : (Y → Bool) → Prot X Y → Prot X Y → Prot X Y

namespace Prot

variable {X Y : Type*}

/-- The output of the protocol on the input pair `(x, y)`. -/
def run : Prot X Y → X → Y → Bool
  | leaf b, _, _ => b
  | alice g L R, x, y => if g x then run L x y else run R x y
  | bob g L R, x, y => if g y then run L x y else run R x y

/-- The communication cost of a protocol: the number of bits exchanged in the
worst case, i.e. the depth of the protocol tree. -/
def cost : Prot X Y → ℕ
  | leaf _ => 0
  | alice _ L R => 1 + max (cost L) (cost R)
  | bob _ L R => 1 + max (cost L) (cost R)

end Prot

/-- The fooling-set bound.  Let `D` be a relation ("the answer is `1`") and let
`(x i, y i)`, `i ∈ A`, be a fooling family: for `i ≠ j` in `A`, one of the
crossed pairs `(x i, y j)`, `(x j, y i)` is a `0`-input.  If a protocol `P`
outputs `true` only on `1`-inputs of the rectangle `px × py`, then any set `B`
of fooling indices accepted by `P` inside that rectangle has at most
`2 ^ cost P` elements. -/
theorem fooling_card_le {X Y ι : Type*} (A : Finset ι) (x : ι → X) (y : ι → Y)
    (D : X → Y → Prop)
    (hfool : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ¬ D (x i) (y j) ∨ ¬ D (x j) (y i)) :
    ∀ (P : Prot X Y) (px : X → Prop) (py : Y → Prop) (B : Finset ι), B ⊆ A →
      (∀ i ∈ B, px (x i) ∧ py (y i) ∧ P.run (x i) (y i) = true) →
      (∀ a b, px a → py b → P.run a b = true → D a b) →
      B.card ≤ 2 ^ P.cost := by
  intro P
  induction P with
  | leaf b =>
    intro px py B hBA hB hsound
    cases b with
    | false =>
      have hempty : B = ∅ := by
        by_contra h
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 h
        have := (hB i hi).2.2
        simp [Prot.run] at this
      simp [hempty]
    | true =>
      have hcost : (Prot.leaf (X := X) (Y := Y) true).cost = 0 := rfl
      rw [hcost, pow_zero]
      apply Finset.card_le_one.2
      intro i hi j hj
      by_contra hij
      have h1 : D (x i) (y j) := hsound _ _ (hB i hi).1 (hB j hj).2.1 rfl
      have h2 : D (x j) (y i) := hsound _ _ (hB j hj).1 (hB i hi).2.1 rfl
      rcases hfool i (hBA hi) j (hBA hj) hij with h | h
      · exact h h1
      · exact h h2
  | alice g L R ihL ihR =>
    intro px py B hBA hB hsound
    have hL : (∀ a b, (px a ∧ g a = true) → py b → L.run a b = true → D a b) := by
      intro a b ha hb hrun
      exact hsound a b ha.1 hb (by simp [Prot.run, ha.2, hrun])
    have hR : (∀ a b, (px a ∧ g a = false) → py b → R.run a b = true → D a b) := by
      intro a b ha hb hrun
      exact hsound a b ha.1 hb (by simp [Prot.run, ha.2, hrun])
    classical
    set B1 := B.filter (fun i => g (x i) = true) with hB1
    set B2 := B.filter (fun i => g (x i) = false) with hB2
    have hcard : B.card ≤ B1.card + B2.card := by
      refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le B1 B2)
      intro i hi
      rw [Finset.mem_union, hB1, hB2, Finset.mem_filter, Finset.mem_filter]
      by_cases hg : g (x i) = true
      · exact Or.inl ⟨hi, hg⟩
      · exact Or.inr ⟨hi, by simpa using hg⟩
    have h1 : B1.card ≤ 2 ^ L.cost := by
      refine ihL (fun a => px a ∧ g a = true) py B1
        (Finset.Subset.trans (Finset.filter_subset _ _) hBA) ?_ hL
      intro i hi
      rw [hB1, Finset.mem_filter] at hi
      obtain ⟨hiB, hg⟩ := hi
      refine ⟨⟨(hB i hiB).1, hg⟩, (hB i hiB).2.1, ?_⟩
      have := (hB i hiB).2.2
      simpa [Prot.run, hg] using this
    have h2 : B2.card ≤ 2 ^ R.cost := by
      refine ihR (fun a => px a ∧ g a = false) py B2
        (Finset.Subset.trans (Finset.filter_subset _ _) hBA) ?_ hR
      intro i hi
      rw [hB2, Finset.mem_filter] at hi
      obtain ⟨hiB, hg⟩ := hi
      refine ⟨⟨(hB i hiB).1, hg⟩, (hB i hiB).2.1, ?_⟩
      have := (hB i hiB).2.2
      simpa [Prot.run, hg] using this
    have hle : (2:ℕ) ^ L.cost + 2 ^ R.cost ≤ 2 ^ (Prot.alice g L R).cost := by
      have e1 : (2:ℕ) ^ L.cost ≤ 2 ^ (max L.cost R.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have e2 : (2:ℕ) ^ R.cost ≤ 2 ^ (max L.cost R.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have e3 : (Prot.alice g L R).cost = 1 + max L.cost R.cost := rfl
      rw [e3, pow_add, pow_one]
      omega
    omega
  | bob g L R ihL ihR =>
    intro px py B hBA hB hsound
    have hL : (∀ a b, px a → (py b ∧ g b = true) → L.run a b = true → D a b) := by
      intro a b ha hb hrun
      exact hsound a b ha hb.1 (by simp [Prot.run, hb.2, hrun])
    have hR : (∀ a b, px a → (py b ∧ g b = false) → R.run a b = true → D a b) := by
      intro a b ha hb hrun
      exact hsound a b ha hb.1 (by simp [Prot.run, hb.2, hrun])
    classical
    set B1 := B.filter (fun i => g (y i) = true) with hB1
    set B2 := B.filter (fun i => g (y i) = false) with hB2
    have hcard : B.card ≤ B1.card + B2.card := by
      refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le B1 B2)
      intro i hi
      rw [Finset.mem_union, hB1, hB2, Finset.mem_filter, Finset.mem_filter]
      by_cases hg : g (y i) = true
      · exact Or.inl ⟨hi, hg⟩
      · exact Or.inr ⟨hi, by simpa using hg⟩
    have h1 : B1.card ≤ 2 ^ L.cost := by
      refine ihL px (fun b => py b ∧ g b = true) B1
        (Finset.Subset.trans (Finset.filter_subset _ _) hBA) ?_ hL
      intro i hi
      rw [hB1, Finset.mem_filter] at hi
      obtain ⟨hiB, hg⟩ := hi
      refine ⟨(hB i hiB).1, ⟨(hB i hiB).2.1, hg⟩, ?_⟩
      have := (hB i hiB).2.2
      simpa [Prot.run, hg] using this
    have h2 : B2.card ≤ 2 ^ R.cost := by
      refine ihR px (fun b => py b ∧ g b = false) B2
        (Finset.Subset.trans (Finset.filter_subset _ _) hBA) ?_ hR
      intro i hi
      rw [hB2, Finset.mem_filter] at hi
      obtain ⟨hiB, hg⟩ := hi
      refine ⟨(hB i hiB).1, ⟨(hB i hiB).2.1, hg⟩, ?_⟩
      have := (hB i hiB).2.2
      simpa [Prot.run, hg] using this
    have hle : (2:ℕ) ^ L.cost + 2 ^ R.cost ≤ 2 ^ (Prot.bob g L R).cost := by
      have e1 : (2:ℕ) ^ L.cost ≤ 2 ^ (max L.cost R.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have e2 : (2:ℕ) ^ R.cost ≤ 2 ^ (max L.cost R.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have e3 : (Prot.bob g L R).cost = 1 + max L.cost R.cost := rfl
      rw [e3, pow_add, pow_one]
      omega
    omega

/-- Two subsets of `Fin n`, given as characteristic vectors, are disjoint. -/
def Disj {n : ℕ} (a b : Fin n → Bool) : Prop := ∀ i, ¬ (a i = true ∧ b i = true)

/-- The complement of a subset of `Fin n`. -/
def cmpl {n : ℕ} (a : Fin n → Bool) : Fin n → Bool := fun i => !a i

theorem disj_self_cmpl {n : ℕ} (a : Fin n → Bool) : Disj a (cmpl a) := by
  intro i h
  simp [cmpl, h.1] at h

/-- The pairs `(S, Sᶜ)` form a fooling set for disjointness. -/
theorem fooling_pairs {n : ℕ} (a b : Fin n → Bool) (hab : a ≠ b) :
    ¬ Disj a (cmpl b) ∨ ¬ Disj b (cmpl a) := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  apply hab
  funext i
  have e1 := h1 i
  have e2 := h2 i
  simp only [cmpl, not_and, Bool.not_eq_true'] at e1 e2
  cases ha : a i <;> cases hb : b i <;> simp [ha, hb] at e1 e2 ⊢

/-- Any deterministic protocol that never wrongly reports disjointness accepts
at most `2 ^ cost` of the `2 ^ n` fooling pairs `(S, Sᶜ)`. -/
theorem accepted_fooling_le {n : ℕ} (P : Prot (Fin n → Bool) (Fin n → Bool))
    (hsound : ∀ a b, P.run a b = true → Disj a b) :
    ((univ : Finset (Fin n → Bool)).filter
      (fun S => P.run S (cmpl S) = true)).card ≤ 2 ^ P.cost := by
  refine fooling_card_le (X := Fin n → Bool) (Y := Fin n → Bool)
    (univ : Finset (Fin n → Bool)) id cmpl Disj
    (fun i _ j _ hij => fooling_pairs i j hij)
    P (fun _ => True) (fun _ => True) _ (Finset.filter_subset _ _) ?_
    (fun a b _ _ hrun => hsound a b hrun)
  intro i hi
  rw [Finset.mem_filter] at hi
  exact ⟨trivial, trivial, hi.2⟩

/-- The `m`-th bit of a subset of `Fin n` (`false` if `m` is out of range). -/
def getBit {n : ℕ} (m : ℕ) (x : Fin n → Bool) : Bool :=
  if h : m < n then x ⟨m, h⟩ else false

/-- The naive protocol: Alice reveals her bits `m-1, …, 0` one at a time, and
Bob finally answers.  The parameter `h` records the answer Bob would give on
the basis of the bits revealed so far. -/
def build {n : ℕ} : ℕ → ((Fin n → Bool) → Bool) → Prot (Fin n → Bool) (Fin n → Bool)
  | 0, h => Prot.bob h (Prot.leaf true) (Prot.leaf false)
  | m + 1, h =>
      Prot.alice (getBit m) (build m (fun y => h y && !(getBit m y))) (build m h)

theorem build_cost {n : ℕ} (m : ℕ) (h : (Fin n → Bool) → Bool) :
    (build m h).cost = m + 1 := by
  induction m generalizing h with
  | zero => rfl
  | succ m ih => simp [build, Prot.cost, ih]; omega

theorem build_run {n : ℕ} (m : ℕ) : ∀ (h : (Fin n → Bool) → Bool) (x y : Fin n → Bool),
    ((build m h).run x y = true ↔
      (h y = true ∧ ∀ i : Fin n, (i : ℕ) < m → ¬ (x i = true ∧ y i = true))) := by
  induction m with
  | zero =>
    intro h x y
    constructor
    · intro hrun
      refine ⟨?_, by omega⟩
      by_contra hy
      simp [build, Prot.run, hy] at hrun
    · intro hy
      simp [build, Prot.run, hy.1]
  | succ m ih =>
    intro h x y
    by_cases hb : getBit m x = true
    · have hm : m < n := by
        by_contra hmn
        rw [getBit, dif_neg hmn] at hb
        exact absurd hb (by simp)
      have hx : x ⟨m, hm⟩ = true := by rwa [getBit, dif_pos hm] at hb
      have hrun : (build (m + 1) h).run x y =
          (build m (fun y => h y && !(getBit m y))).run x y := by
        simp [build, Prot.run, hb]
      rw [hrun, ih]
      constructor
      · rintro ⟨h1, h2⟩
        rw [Bool.and_eq_true] at h1
        refine ⟨h1.1, ?_⟩
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hi'
        · exact h2 i hi'
        · have : i = ⟨m, hm⟩ := by
            apply Fin.ext; simpa using hi'
          subst this
          have : getBit m y = false := by simpa using h1.2
          rw [getBit, dif_pos hm] at this
          simp [this]
      · rintro ⟨h1, h2⟩
        refine ⟨?_, fun i hi => h2 i (by omega)⟩
        rw [Bool.and_eq_true]
        refine ⟨h1, ?_⟩
        have := h2 ⟨m, hm⟩ (by simp)
        rw [hx] at this
        have hy : y ⟨m, hm⟩ = false := by
          rcases Bool.eq_false_or_eq_true (y ⟨m, hm⟩) with h' | h'
          · exact absurd ⟨rfl, h'⟩ this
          · exact h'
        simp [getBit, dif_pos hm, hy]
    · have hb' : getBit m x = false := by simpa using hb
      have hrun : (build (m + 1) h).run x y = (build m h).run x y := by
        simp [build, Prot.run, hb']
      rw [hrun, ih]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hi'
        · exact h2 i hi'
        · have hm : m < n := hi' ▸ i.isLt
          have hxi : x i = false := by
            rw [getBit, dif_pos hm] at hb'
            rwa [show (⟨m, hm⟩ : Fin n) = i from Fin.ext hi'.symm] at hb'
          simp [hxi]
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun i hi => h2 i (by omega)⟩

/-- **Upper bound**: there is a correct deterministic protocol for disjointness
on `Fin n` of cost `n + 1`, so the lower bound below is not vacuous and is
tight up to an additive constant. -/
theorem disjointness_ub (n : ℕ) :
    ∃ P : Prot (Fin n → Bool) (Fin n → Bool),
      (∀ a b, P.run a b = true ↔ Disj a b) ∧ P.cost = n + 1 := by
  refine ⟨build n (fun _ => true), fun a b => ?_, build_cost n _⟩
  rw [build_run]
  constructor
  · rintro ⟨-, h2⟩
    intro i
    exact h2 i i.isLt
  · intro h
    exact ⟨rfl, fun i _ => h i⟩

/-- **Randomized lower bound for set disjointness.**

Consider a public-coin randomized protocol for set disjointness on the ground
set `Fin n`: a family `P r` of deterministic protocols indexed by a finite
nonempty set `R` of random strings (uniformly distributed), each of cost at
most `c`.  Assume the protocol is sound (it outputs `true` only on genuinely
disjoint pairs) and that on every disjoint pair it outputs `true` with
probability at least `1/2`.  Then `c ≥ n - 1`; that is, the randomized
communication complexity of disjointness is `Ω(n)`. -/
theorem disjointness_lb {n c : ℕ} {R : Type*} [Fintype R] [Nonempty R]
    (P : R → Prot (Fin n → Bool) (Fin n → Bool))
    (hcost : ∀ r, (P r).cost ≤ c)
    (hsound : ∀ r a b, (P r).run a b = true → Disj a b)
    (hcomplete : ∀ a b, Disj a b →
      Fintype.card R ≤ 2 * ((univ : Finset R).filter
        (fun r => (P r).run a b = true)).card) :
    n ≤ c + 1 := by
  classical
  -- double counting of the set of pairs `(S, r)` with `P r` accepting `(S, Sᶜ)`
  set T : ℕ := ∑ r : R, ∑ S : Fin n → Bool,
    (if (P r).run S (cmpl S) = true then 1 else 0) with hT
  have hupper : T ≤ Fintype.card R * 2 ^ c := by
    have hrow : ∀ r : R, (∑ S : Fin n → Bool,
        (if (P r).run S (cmpl S) = true then 1 else 0)) ≤ 2 ^ c := by
      intro r
      have h1 := accepted_fooling_le (P r) (hsound r)
      have h2 : (2:ℕ) ^ (P r).cost ≤ 2 ^ c :=
        Nat.pow_le_pow_right (by norm_num) (hcost r)
      calc (∑ S : Fin n → Bool, (if (P r).run S (cmpl S) = true then 1 else 0))
          = ((univ : Finset (Fin n → Bool)).filter
              (fun S => (P r).run S (cmpl S) = true)).card := by
            rw [Finset.card_filter]
        _ ≤ 2 ^ (P r).cost := h1
        _ ≤ 2 ^ c := h2
    calc T ≤ ∑ _r : R, 2 ^ c := Finset.sum_le_sum (fun r _ => hrow r)
      _ = Fintype.card R * 2 ^ c := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hlower : 2 ^ n * Fintype.card R ≤ 2 * T := by
    have hswap : T = ∑ S : Fin n → Bool, ∑ r : R,
        (if (P r).run S (cmpl S) = true then 1 else 0) := Finset.sum_comm
    have hS : ∀ S : Fin n → Bool, Fintype.card R ≤
        2 * ∑ r : R, (if (P r).run S (cmpl S) = true then 1 else 0) := by
      intro S
      have h := hcomplete S (cmpl S) (disj_self_cmpl S)
      rwa [Finset.card_filter] at h
    calc 2 ^ n * Fintype.card R
        = ∑ _S : Fin n → Bool, Fintype.card R := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          congr 1
          simp
      _ ≤ ∑ S : Fin n → Bool,
            2 * ∑ r : R, (if (P r).run S (cmpl S) = true then 1 else 0) :=
          Finset.sum_le_sum (fun S _ => hS S)
      _ = 2 * T := by rw [hswap, Finset.mul_sum]
  have hcardpos : 0 < Fintype.card R := Fintype.card_pos
  have key : (2:ℕ) ^ n ≤ 2 ^ (c + 1) := by
    have h : 2 ^ n * Fintype.card R ≤ 2 ^ (c + 1) * Fintype.card R := by
      calc 2 ^ n * Fintype.card R ≤ 2 * T := hlower
        _ ≤ 2 * (Fintype.card R * 2 ^ c) := by omega
        _ = 2 ^ (c + 1) * Fintype.card R := by ring
    exact Nat.le_of_mul_le_mul_right h hcardpos
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 key

/-- **Deterministic lower bound for set disjointness**: a single correct
deterministic protocol for disjointness on `Fin n` costs at least `n` bits. -/
theorem disjointness_deterministic_lb {n : ℕ}
    (P : Prot (Fin n → Bool) (Fin n → Bool))
    (hcorrect : ∀ a b, (P.run a b = true ↔ Disj a b)) :
    n ≤ P.cost := by
  classical
  have h := accepted_fooling_le P (fun a b hab => (hcorrect a b).1 hab)
  have hall : ((univ : Finset (Fin n → Bool)).filter
      (fun S => P.run S (cmpl S) = true)) = univ := by
    apply Finset.filter_true_of_mem
    intro S _
    exact (hcorrect S (cmpl S)).2 (disj_self_cmpl S)
  rw [hall, Finset.card_univ] at h
  have hc : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  rw [hc] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

end CS

