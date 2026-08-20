import Mathlib
/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
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

namespace Phys

open MeasureTheory Filter Topology

/-- The auxiliary ("virial current") function
`F x = c * (x * ψ'(x)^2 + ψ(x) * ψ'(x)) - x * (V x - E) * ψ x ^ 2`
attached to a solution of the stationary Schrödinger equation
`-c * ψ'' + V ψ = E ψ` (here `c = ℏ²/2m`). -/

theorem integrable_sq_mul_gaussian :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2)) volume := by
  have hg : Integrable (fun x : ℝ => 2 * Real.exp (-(1/2 : ℝ) * x ^ 2)) volume :=
    (integrable_exp_neg_mul_sq (by norm_num)).const_mul 2
  refine Integrable.mono' hg
    ((continuous_pow 2).mul
      (Real.continuous_exp.comp (continuous_pow 2).neg)).aestronglyMeasurable ?_
  filter_upwards with x
  have h1 : x ^ 2 / 2 + 1 ≤ Real.exp (x ^ 2 / 2) := Real.add_one_le_exp _
  have hpos : (0:ℝ) < Real.exp (x ^ 2 / 2) := Real.exp_pos _
  have hApos : (0:ℝ) < Real.exp (-(1/2:ℝ) * x ^ 2) := Real.exp_pos _
  have hx : Real.exp (-x ^ 2) = Real.exp (-(1/2:ℝ) * x ^ 2) / Real.exp (x ^ 2 / 2) := by
    rw [eq_div_iff (ne_of_gt hpos), ← Real.exp_add]; ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hx, mul_div_assoc', div_le_iff₀ hpos]
  nlinarith [hApos, h1, sq_nonneg x]

/-- `exp (-x²/2) ^ 2 = exp (-x²)`. -/
