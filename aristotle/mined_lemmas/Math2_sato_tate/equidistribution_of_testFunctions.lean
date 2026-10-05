/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Real MeasureTheory
open scoped Topology BigOperators Classical

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The Sato–Tate density `(2/π) sin²θ` on `[0, π]`. -/

lemma equidistribution_of_testFunctions {θ : ℕ → ℝ} {N : ℕ → ℝ}
    (hN : ∀ X, 0 ≤ N X)
    (hST : ∀ f : ℝ → ℝ, Continuous f →
      Tendsto (fun X => (∑ p ∈ Nat.primesBelow X, f (θ p)) / N X) atTop
        (𝓝 (∫ x in (0:ℝ)..π, f x * stDensity x)))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π) :
    Tendsto
      (fun X => (((Nat.primesBelow X).filter (fun p => θ p ∈ Set.Icc a b)).card : ℝ) / N X)
      atTop (𝓝 (stCDF b - stCDF a)) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := min 1 (π * ε / 16) with hδdef
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδε : (4 / π) * δ ≤ ε / 4 := by
    have h1 : δ ≤ π * ε / 16 := min_le_right _ _
    have h2 : (4 / π) * δ ≤ (4 / π) * (π * ε / 16) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (4 / π) * (π * ε / 16) = ε / 4 := by field_simp; ring
    linarith
  obtain ⟨X1, hX1⟩ := Metric.tendsto_atTop.1
    (hST (trap (a - δ) (b + δ) δ) (continuous_trap _ _ _)) (ε / 4) (by linarith)
  obtain ⟨X2, hX2⟩ := Metric.tendsto_atTop.1
    (hST (trap a b δ) (continuous_trap _ _ _)) (ε / 4) (by linarith)
  refine ⟨max X1 X2, fun X hX => ?_⟩
  have h1 := hX1 X (le_of_max_le_left hX)
  have h2 := hX2 X (le_of_max_le_right hX)
  rw [Real.dist_eq, abs_lt] at h1 h2
  have hdiv : ∀ x y : ℝ, x ≤ y → x / N X ≤ y / N X := by
    intro x y h
    rcases (hN X).lt_or_eq with h0 | h0
    · gcongr
    · simp [← h0]
  have hcard : (((Nat.primesBelow X).filter (fun p => θ p ∈ Set.Icc a b)).card : ℝ)
      = ∑ p ∈ Nat.primesBelow X, if θ p ∈ Set.Icc a b then (1:ℝ) else 0 := by
    rw [Finset.card_filter]
    push_cast
    rfl
  have hup : (((Nat.primesBelow X).filter (fun p => θ p ∈ Set.Icc a b)).card : ℝ) / N X
      ≤ (∑ p ∈ Nat.primesBelow X, trap (a - δ) (b + δ) δ (θ p)) / N X := by
    rw [hcard]
    refine hdiv _ _ (Finset.sum_le_sum ?_)
    intro p _
    by_cases hp : θ p ∈ Set.Icc a b
    · rw [if_pos hp, trap_eq_one hδ (by have := hp.1; linarith) (by have := hp.2; linarith)]
    · rw [if_neg hp]
      exact trap_nonneg _ _ _ _
  have hlow : (∑ p ∈ Nat.primesBelow X, trap a b δ (θ p)) / N X
      ≤ (((Nat.primesBelow X).filter (fun p => θ p ∈ Set.Icc a b)).card : ℝ) / N X := by
    rw [hcard]
    refine hdiv _ _ (Finset.sum_le_sum ?_)
    intro p _
    by_cases hp : θ p ∈ Set.Icc a b
    · rw [if_pos hp]
      exact trap_le_one _ _ _ _
    · rw [if_neg hp]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hp
      rcases hp with hp | hp
      · exact le_of_eq (trap_eq_zero_left hδ hp.le)
      · exact le_of_eq (trap_eq_zero_right hδ hp.le)
  have hI1 := integral_trap_outer_le hδ ha hab hb
  have hI2 := integral_trap_inner_ge hδ ha hab hb
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ## Chebyshev polynomials and the Sato–Tate measure -/

/-- `UBasis k x = U_k(cos x)`, where `U_k` is the `k`-th Chebyshev polynomial of the second
kind.  Equivalently `UBasis k x = sin ((k+1) x) / sin x`; these are the traces of the
symmetric powers of a `SU(2)`-conjugacy class with angle `x`. -/
