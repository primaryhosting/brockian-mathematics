import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

namespace Frontier

open MeasureTheory

/-! ## Basic objects -/

/-- Physical space `ℝ^d`, with its Euclidean structure and Lebesgue measure. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Negative part `t⁻ = max (-t) 0` of a real number. -/

lemma coulomb_le_of_hardy_pointwise {Z a : ℝ} (hZ : 0 < Z) (ha : 0 ≤ a) (v : ℝ) :
    v ^ 2 / a ≤ (4 * Z)⁻¹ * (v ^ 2 / a ^ 2) + Z * v ^ 2 := by
  rcases eq_or_lt_of_le ha with h | h
  · simp [← h]; positivity
  · have key : (4*Z)⁻¹ * (v^2/a^2) + Z*v^2 - v^2/a = v^2*(2*Z*a-1)^2/(4*Z*a^2) := by
      field_simp; ring
    nlinarith [div_nonneg (mul_nonneg (sq_nonneg v) (sq_nonneg (2*Z*a-1)))
      (by positivity : (0:ℝ) ≤ 4*Z*a^2)]

/-- **Base case of stability of matter: the hydrogenic atom.**  Given Hardy's inequality,
a single electron in the field of one nucleus of charge `Z` has energy at least `-Z²`. -/
