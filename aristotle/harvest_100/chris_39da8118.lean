import Mathlib

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

open scoped BigOperators
open scoped Classical
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian
namespace BetrothedNumbers

/-! ## Betrothed (quasi-amicable) numbers -/

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: they are distinct positive
integers whose sums of divisors both equal `n + m + 1`, i.e. each is the sum of the
proper divisors, excluding `1`, of the other. -/
def IsBetrothedPair (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧ n ≠ m ∧ σ 1 n = n + m + 1 ∧ σ 1 m = n + m + 1

/-- The set of betrothed numbers: those belonging to some betrothed pair. -/
def betrothedSet : Set ℕ := {n | ∃ m, IsBetrothedPair n m}

/-! ## Counting function and density -/

/-- `count A x` is the number of elements of `A` that are `< x`. -/
noncomputable def count (A : Set ℕ) (x : ℕ) : ℕ :=
  ((Finset.range x).filter (fun n => n ∈ A)).card

/-- `A` has asymptotic density zero. -/
def HasDensityZero (A : Set ℕ) : Prop :=
  Filter.Tendsto (fun x : ℕ => (count A x : ℝ) / x) Filter.atTop (nhds 0)

/-! ## Reusable counting toolkit -/

theorem count_le (A : Set ℕ) (x : ℕ) : count A x ≤ x := by
  simpa [count] using Finset.card_filter_le (Finset.range x) (fun n => n ∈ A)

theorem count_mono {A B : Set ℕ} (h : A ⊆ B) (x : ℕ) : count A x ≤ count B x := by
  refine Finset.card_le_card ?_
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1, h hn.2⟩

theorem count_union_le (A B : Set ℕ) (x : ℕ) :
    count (A ∪ B) x ≤ count A x + count B x := by
  unfold count
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Set.mem_union] at hn ⊢
  tauto

theorem count_le_diff_add (A B : Set ℕ) (x : ℕ) :
    count A x ≤ count B x + count (A \ B) x := by
  calc count A x ≤ count (B ∪ (A \ B)) x := count_mono (fun n hn => by
        by_cases h : n ∈ B
        · exact Or.inl h
        · exact Or.inr ⟨hn, h⟩) x
    _ ≤ _ := count_union_le _ _ x

/-- Criterion for density zero: for every `ε > 0` the counting function is eventually
at most `ε x`. -/
theorem hasDensityZero_of_eventually_le {A : Set ℕ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ x ≥ N, (count A x : ℝ) ≤ ε * x) :
    HasDensityZero A := by
  rw [HasDensityZero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by linarith)
  refine ⟨max N 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right N 1) hx
  have hxN : N ≤ x := le_trans (le_max_left N 1) hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  have h1 : (count A x : ℝ) ≤ (ε / 2) * x := hN x hxN
  have h0 : (0 : ℝ) ≤ (count A x : ℝ) / x := div_nonneg (by positivity) (le_of_lt hxpos)
  have h2 : (count A x : ℝ) / x ≤ ε / 2 := by rw [div_le_iff₀ hxpos]; exact h1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

/-- The converse criterion: density zero gives eventual bounds `count A x ≤ ε x`. -/
theorem HasDensityZero.eventually_le {A : Set ℕ} (hA : HasDensityZero A)
    (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ x ≥ N, (count A x : ℝ) ≤ ε * x := by
  rw [HasDensityZero, Metric.tendsto_atTop] at hA
  obtain ⟨N, hN⟩ := hA ε hε
  refine ⟨max N 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right N 1) hx
  have hxN : N ≤ x := le_trans (le_max_left N 1) hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  have := hN x hxN
  rw [Real.dist_eq, sub_zero] at this
  have h2 : (count A x : ℝ) / x ≤ ε := le_of_lt (lt_of_abs_lt this)
  rwa [div_le_iff₀ hxpos] at h2

/-- Density zero is inherited by subsets. -/
theorem HasDensityZero.subset {A B : Set ℕ} (hB : HasDensityZero B) (hAB : A ⊆ B) :
    HasDensityZero A := by
  refine hasDensityZero_of_eventually_le (fun ε hε => ?_)
  obtain ⟨N, hN⟩ := hB.eventually_le ε hε
  refine ⟨N, fun x hx => ?_⟩
  have h4 : (count A x : ℝ) ≤ (count B x : ℝ) := by exact_mod_cast count_mono hAB x
  exact le_trans h4 (hN x hx)

/-- A finite union of density-zero sets has density zero. -/
theorem HasDensityZero.union {A B : Set ℕ} (hA : HasDensityZero A) (hB : HasDensityZero B) :
    HasDensityZero (A ∪ B) := by
  refine hasDensityZero_of_eventually_le (fun ε hε => ?_)
  obtain ⟨N₁, hN₁⟩ := hA.eventually_le (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hB.eventually_le (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun x hx => ?_⟩
  have h1 := hN₁ x (le_trans (le_max_left _ _) hx)
  have h2 := hN₂ x (le_trans (le_max_right _ _) hx)
  have h3 : (count (A ∪ B) x : ℝ) ≤ (count A x : ℝ) + (count B x : ℝ) := by
    exact_mod_cast count_union_le A B x
  linarith

/-! ## Two elementary density-zero estimates -/

/-- The number of multiples of `d` below `x` is at most `x / d + 1`. -/
theorem count_multiples_le (d x : ℕ) (hd : 0 < d) :
    count {n : ℕ | d ∣ n} x ≤ x / d + 1 := by
  unfold count
  refine le_trans (Finset.card_le_card
      (t := (Finset.range (x / d + 1)).image (fun k => d * k)) ?_)
    (le_trans Finset.card_image_le (by simp))
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hn
  obtain ⟨hlt, k, rfl⟩ := hn
  refine Finset.mem_image.2 ⟨k, ?_, rfl⟩
  simp only [Finset.mem_range]
  have h1 : k = d * k / d := by rw [Nat.mul_div_cancel_left _ hd]
  have hk : d * k / d ≤ x / d := Nat.div_le_div_right (le_of_lt hlt)
  omega

/-- The number of perfect squares below `x` is at most `√x + 1`. -/
theorem count_squares_le (x : ℕ) : count {n : ℕ | IsSquare n} x ≤ Nat.sqrt x + 1 := by
  unfold count
  refine le_trans (Finset.card_le_card
      (t := (Finset.range (Nat.sqrt x + 1)).image (fun k => k * k)) ?_)
    (le_trans Finset.card_image_le (by simp))
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hn
  obtain ⟨hlt, r, rfl⟩ := hn
  refine Finset.mem_image.2 ⟨r, ?_, rfl⟩
  simp only [Finset.mem_range]
  have h1 : r ≤ Nat.sqrt (r * r) := by simp
  have h2 : Nat.sqrt (r * r) ≤ Nat.sqrt x := Nat.sqrt_le_sqrt (le_of_lt hlt)
  omega

/-- The set of perfect squares has density zero. -/
theorem hasDensityZero_squares : HasDensityZero {n : ℕ | IsSquare n} := by
  refine hasDensityZero_of_eventually_le (fun ε hε => ?_)
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      have : (0 : ℝ) < 2 / ε := by positivity
      simp only [Nat.cast_zero] at hk
      linarith
    · exact h
  refine ⟨(k + 1) * (k + 1), fun x hx => ?_⟩
  have hxk : k ≤ Nat.sqrt x := by
    have hkk : k * k ≤ x := by nlinarith
    exact Nat.le_sqrt.2 hkk
  have hsq : Nat.sqrt x * Nat.sqrt x ≤ x := by
    have := Nat.sqrt_le' x
    nlinarith [this, sq (Nat.sqrt x)]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hxpos : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have key : (k : ℝ) * ((Nat.sqrt x : ℝ) + 1) ≤ 2 * x := by
    have h1 : k * (Nat.sqrt x + 1) ≤ 2 * x := by
      have hmul : k * Nat.sqrt x ≤ Nat.sqrt x * Nat.sqrt x := Nat.mul_le_mul_right _ hxk
      have hk1 : k ≤ x := le_trans hxk (Nat.sqrt_le_self x)
      nlinarith
    exact_mod_cast h1
  have hεk : 2 / (k : ℝ) ≤ ε := by
    rw [div_le_iff₀ hkR]
    rw [div_lt_iff₀ hε] at hk
    nlinarith
  have h1 : (count {n : ℕ | IsSquare n} x : ℝ) ≤ (Nat.sqrt x : ℝ) + 1 := by
    have := count_squares_le x
    have : (count {n : ℕ | IsSquare n} x : ℝ) ≤ ((Nat.sqrt x + 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    simpa using this
  have hstep : (Nat.sqrt x : ℝ) + 1 ≤ (2 / (k : ℝ)) * x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hkR]
    nlinarith [key]
  calc (count {n : ℕ | IsSquare n} x : ℝ) ≤ (Nat.sqrt x : ℝ) + 1 := h1
    _ ≤ (2 / (k : ℝ)) * x := hstep
    _ ≤ ε * x := mul_le_mul_of_nonneg_right hεk hxpos

/-! ## Structure of betrothed numbers -/

theorem IsBetrothedPair.symm {n m : ℕ} (h : IsBetrothedPair n m) : IsBetrothedPair m n := by
  obtain ⟨hn, hm, hne, h1, h2⟩ := h
  refine ⟨hm, hn, hne.symm, ?_, ?_⟩ <;> omega

/-- The partner of a betrothed number is uniquely determined: `m = σ₁(n) - n - 1`. -/
theorem IsBetrothedPair.partner_eq {n m : ℕ} (h : IsBetrothedPair n m) :
    m = σ 1 n - n - 1 := by
  obtain ⟨-, -, -, h1, -⟩ := h
  omega

theorem IsBetrothedPair.unique {n m m' : ℕ} (h : IsBetrothedPair n m)
    (h' : IsBetrothedPair n m') : m = m' := by
  rw [h.partner_eq, h'.partner_eq]

/-- A one-variable description of the betrothed numbers: the partner is forced to be
`σ₁(n) - n - 1`, so membership in `betrothedSet` is a condition on `n` alone. -/
theorem mem_betrothedSet_iff (n : ℕ) :
    n ∈ betrothedSet ↔
      0 < n ∧ n + 1 < σ 1 n ∧ σ 1 n - n - 1 ≠ n ∧
        σ 1 (σ 1 n - n - 1) = σ 1 n := by
  constructor
  · rintro ⟨m, hn, hmpos, hne, h1, h2⟩
    have hmeq : m = σ 1 n - n - 1 := by omega
    subst hmeq
    exact ⟨hn, by omega, fun h => hne h.symm, by omega⟩
  · rintro ⟨hn, hlt, hne, hσ⟩
    exact ⟨σ 1 n - n - 1, hn, by omega, fun h => hne h.symm, by omega, by omega⟩

/-- Every betrothed number `n` satisfies `σ₁(n) > n + 1`. -/
theorem betrothed_sigma_gt {n : ℕ} (hn : n ∈ betrothedSet) : n + 1 < σ 1 n := by
  obtain ⟨m, hn0, hm0, -, h1, -⟩ := hn
  omega

/-! ## The reduction theorem -/

/--
**Density zero reduction for betrothed numbers.**

This is the combinatorial skeleton of Pollack's theorem that the betrothed
(quasi-amicable) numbers have asymptotic density zero, following the Erdős
exceptional-set scheme. The two genuinely analytic inputs are isolated as
hypotheses:

* `hExceptional`: a family `E k` of exceptional sets (in the Erdős/Pollack argument,
  the integers whose factorisation, or whose value of `σ(n)/n`, is atypical at level `k`)
  whose upper density tends to `0` as the level `k` grows;
* `hMain`: for each fixed level `k`, the betrothed numbers *outside* the exceptional set
  `E k` are counted, by the main divisor-sum argument, by at most `x/(k+1)` up to `x`.

From these the theorem concludes that the betrothed numbers have density zero.
No analytic input is assumed beyond the two explicitly stated hypotheses.
-/
theorem density_zero_reduction
    (E : ℕ → Set ℕ)
    (hExceptional : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k ≥ K,
      ∃ N : ℕ, ∀ x ≥ N, (count (E k) x : ℝ) ≤ ε * x)
    (hMain : ∀ k : ℕ, ∃ N : ℕ, ∀ x ≥ N,
      (count (betrothedSet \ E k) x : ℝ) ≤ x / (k + 1)) :
    HasDensityZero betrothedSet := by
  refine hasDensityZero_of_eventually_le (fun ε hε => ?_)
  obtain ⟨K, hK⟩ := hExceptional (ε / 2) (by linarith)
  obtain ⟨j, hj⟩ := exists_nat_gt (2 / ε)
  set k := max K j with hkdef
  obtain ⟨N₁, hN₁⟩ := hK k (le_max_left _ _)
  obtain ⟨N₂, hN₂⟩ := hMain k
  refine ⟨max N₁ N₂, fun x hx => ?_⟩
  have hx1 : N₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : N₂ ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hb : (count betrothedSet x : ℝ) ≤
      (count (E k) x : ℝ) + (count (betrothedSet \ E k) x : ℝ) := by
    exact_mod_cast count_le_diff_add betrothedSet (E k) x
  have h1 : (count (E k) x : ℝ) ≤ (ε / 2) * x := hN₁ x hx1
  have h2 : (count (betrothedSet \ E k) x : ℝ) ≤ x / (k + 1) := hN₂ x hx2
  have hjk : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_max_right K j
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h3 : (x : ℝ) / (k + 1) ≤ (ε / 2) * x := by
    rw [div_le_iff₀ hkpos]
    have hεj : 2 / ε ≤ (k : ℝ) := le_trans (le_of_lt hj) hjk
    have h4 : 2 ≤ ε * k := by rw [div_le_iff₀ hε] at hεj; linarith
    nlinarith
  linarith

end BetrothedNumbers
end Brockian

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

