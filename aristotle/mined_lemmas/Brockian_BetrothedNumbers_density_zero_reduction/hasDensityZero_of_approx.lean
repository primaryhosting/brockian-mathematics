import Mathlib
/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Filter Finset

/-! ## Natural density -/

/-- The number of elements of `A` in the interval `[1, N]`. -/

lemma hasDensityZero_of_approx {A : Set ℕ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ B : Set ℕ, HasDensityZero B ∧
      ∀ N : ℕ, (countUpTo A N : ℝ) ≤ countUpTo B N + ε * N) :
    HasDensityZero A := by
  unfold HasDensityZero at *
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨B, hB, hAB⟩ := h (ε / 4) (by linarith)
  rw [Metric.tendsto_atTop] at hB
  obtain ⟨N₀, hN₀⟩ := hB (ε / 4) (by linarith)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  have h1 := hN₀ N (le_trans (le_max_left _ _) hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h1 ⊢
  have h2 : (countUpTo A N : ℝ) / N ≤ (countUpTo B N : ℝ) / N + ε / 4 := by
    rw [div_add' _ _ _ (ne_of_gt hNpos), div_le_div_iff_of_pos_right hNpos]
    have := hAB N
    linarith
  linarith

/-! ## Analytic input: the average order of `σ(n)/n` -/

