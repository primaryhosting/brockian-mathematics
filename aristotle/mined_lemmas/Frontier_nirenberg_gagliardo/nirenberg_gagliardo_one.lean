/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open MeasureTheory Module

namespace Frontier

/-- **The Gagliardo–Nirenberg(–Sobolev) interpolation inequality** on `ℝⁿ`.

Let `n ≥ 1`, let `1 ≤ p` and let `p'` be the Sobolev conjugate exponent of `p`, i.e.
`1 / p' = 1 / p - 1 / n`.  Then there is a constant `C`, depending only on `n` and `p`
(and not on the function), such that for every continuously differentiable, compactly
supported `u : ℝⁿ → ℝ` one has

`‖u‖_{L^{p'}} ≤ C * ‖Du‖_{L^p}`.

This is proved by specialising Mathlib's Gagliardo–Nirenberg–Sobolev inequality
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` to `E = EuclideanSpace ℝ (Fin n)` with the
Lebesgue (Haar) measure and `F = ℝ`; the admissible constant is Mathlib's
`MeasureTheory.SNormLESNormFDerivOfEqConst`. -/

theorem nirenberg_gagliardo_one (n : ℕ) (hn : 2 ≤ n) (p' : NNReal)
    (hp' : (p' : ℝ)⁻¹ = 1 - (n : ℝ)⁻¹) :
    ∃ C : NNReal, ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 u → HasCompactSupport u →
        eLpNorm u p' volume ≤ C * eLpNorm (fderiv ℝ u) 1 volume := by
  refine nirenberg_gagliardo n (by omega) 1 p' le_rfl ?_
  simpa using hp'

end Frontier

