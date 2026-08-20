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
# Weighted Weyl bridge for Liouville correlation

This module proves an **analytic transfer theorem**: for a bounded complex weight `w`
and an arbitrary real sequence `x`, vanishing of the weighted Weyl sums against *every*
Fourier mode `fourier k` (including the trivial mode `k = 0`) forces vanishing of the
weighted averages against *every* continuous observable on the circle `𝕋 = AddCircle 1`.

The point of the module is to isolate the genuinely open arithmetic input.  Nothing here
proves any cancellation for the Liouville function: the Fourier cancellation is carried as
an *explicit hypothesis* in every statement below.

## Status labels

* `Frontier.Spectral.weighted_weyl_correlation` — **STANDARD**: a kernel-verified,
  unconditional theorem of functional analysis (density of the Fourier span in
  `C(𝕋, ℂ)` plus a uniform `‖·‖ ≤ 1` bound, via a `3ε` argument).
* `Frontier.Spectral.liouville_continuous_correlation_of_fourier` — **CONDITIONAL**:
  the Fourier-cancellation input `hfourier` is an explicit, unproved hypothesis.  This is
  *not* a proof of Chowla's conjecture, of Sarnak's conjecture, or of any unconditional
  decorrelation statement for `λ(n)`.
-/
import Mathlib

open Filter Topology Finset Submodule Set

noncomputable section

namespace Frontier.Spectral

/-- The circle `𝕋 = ℝ / ℤ`, realised as `AddCircle (1 : ℝ)`. -/
abbrev Torus : Type := AddCircle (1 : ℝ)

instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The weighted Weyl average
`weightedAvg w x F N = N⁻¹ * ∑_{n < N} w n * F (x n mod 1)`. -/

theorem norm_weightedAvg_le (hw : ∀ n, ‖w n‖ ≤ 1) (F : C(Torus, ℂ)) (N : ℕ) :
    ‖weightedAvg w x F N‖ ≤ ‖F‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [weightedAvg]
  have hFnn : (0 : ℝ) ≤ ‖F‖ := norm_nonneg F
  have hsum : ‖∑ n ∈ Finset.range N, w n * F ((x n : ℝ) : Torus)‖ ≤ (N : ℝ) * ‖F‖ := by
    calc ‖∑ n ∈ Finset.range N, w n * F ((x n : ℝ) : Torus)‖
        ≤ ∑ n ∈ Finset.range N, ‖w n * F ((x n : ℝ) : Torus)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, ‖F‖ := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [norm_mul]
          calc ‖w n‖ * ‖F ((x n : ℝ) : Torus)‖ ≤ 1 * ‖F‖ := by
                exact mul_le_mul (hw n) (F.norm_coe_le_norm _) (norm_nonneg _) zero_le_one
            _ = ‖F‖ := one_mul _
      _ = (N : ℝ) * ‖F‖ := by simp
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [weightedAvg, norm_mul, norm_inv, Complex.norm_natCast]
  rw [inv_mul_le_iff₀ hNpos]
  linarith [hsum]

/-- Vanishing of the weighted averages propagates from the Fourier modes to their
linear span. -/
