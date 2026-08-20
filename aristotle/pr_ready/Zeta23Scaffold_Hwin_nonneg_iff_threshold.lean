/-!
# Hwin Nonneg Iff Threshold
Category: A Assembly
Target: Zeta23Scaffold.Hwin_nonneg_iff_threshold
Statement: H(lambda) >= 0 iff lambda >= 3 - sqrt 6 = 0.5505... on 0 < lambda <= 1 (preprint eq. (1.3), third line, second equivalence -- the degeneration threshold of the method).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The "window" function `H(λ) = 2 - 1/λ - λ/3`. -/
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- On `0 < λ ≤ 1`, we have `H(λ) ≥ 0` iff `λ ≥ 3 - √6 = 0.5505…`. -/
theorem Hwin_nonneg_iff_threshold (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 1) :
    0 ≤ Hwin lam ↔ 3 - Real.sqrt 6 ≤ lam := by
  have h6 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have key : Hwin lam * (3 * lam) = -(lam ^ 2 - 6 * lam + 3) := by
    rw [Hwin]; field_simp; ring
  have h3lam : 0 < 3 * lam := by linarith
  constructor
  · intro h
    have hq : lam ^ 2 - 6 * lam + 3 ≤ 0 := by
      nlinarith [mul_nonneg h (le_of_lt h3lam)]
    nlinarith [h6, Real.sqrt_nonneg 6]
  · intro h
    have hq : lam ^ 2 - 6 * lam + 3 ≤ 0 := by nlinarith [h6]
    have hmul : 0 ≤ Hwin lam * (3 * lam) := by rw [key]; linarith
    exact nonneg_of_mul_nonneg_right (by linarith [hmul, mul_comm (Hwin lam) (3 * lam)]) h3lam

end Zeta23Scaffold


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

