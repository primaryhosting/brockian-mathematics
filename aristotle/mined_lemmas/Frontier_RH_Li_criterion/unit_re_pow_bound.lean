/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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

namespace Frontier

open Complex Filter

/-!
## Elementary complex-analytic estimates
-/

/-- Geometric bound: `|1 - r ^ n| ≤ n |1 - r| max(1,r) ^ n` for real `r ≥ 0`. -/

theorem unit_re_pow_bound (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) :
    1 - (w ^ n).re ≤ (n : ℝ) ^ 2 * (1 - w.re) := by
  have key : ∀ v : ℂ, ‖v‖ = 1 → 1 - v.re = ‖1 - v‖ ^ 2 / 2 := by
    intro v hv
    have h2 : Complex.normSq v = 1 := by
      have := Complex.sq_norm v; rw [hv] at this; simpa using this.symm
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, zero_sub, neg_mul] at h2 ⊢
    nlinarith [h2]
  have hwn : ‖w ^ n‖ = 1 := by rw [norm_pow, hw, one_pow]
  rw [key _ hwn, key _ hw]
  have h1 := norm_one_sub_pow_le w hw.le n
  have h0 : (0 : ℝ) ≤ ‖1 - w‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖1 - w ^ n‖ := norm_nonneg _
  nlinarith [h1, h0, h2, sq_nonneg ((n : ℝ) * ‖1 - w‖ - ‖1 - w ^ n‖)]

/-- Master estimate. With `d = 1 - Re z` and `e = max 0 (‖z‖ - 1)`,
`|1 - Re (z ^ n)| ≤ 2 n ^ 2 (1 + e) ^ n (d + 2 e)` for all `n ≥ 1`. -/
