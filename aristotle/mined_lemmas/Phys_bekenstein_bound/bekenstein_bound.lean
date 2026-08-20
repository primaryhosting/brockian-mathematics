import Mathlib

/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Real

/-- The Bekenstein–Hawking entropy `S = k c³ A / (4 G ℏ)` of a black hole whose horizon
has radius `r` (so horizon area `A = 4π r²`), in terms of Boltzmann's constant `k`,
Newton's constant `G`, the reduced Planck constant `hbar` and the speed of light `c`. -/

theorem bekenstein_bound {k G hbar c R E S : ℝ} (hk : 0 < k) (hG : 0 < G) (hhbar : 0 < hbar)
    (hc : 0 < c) (hE : 0 ≤ E) (hfit : schwarzschildRadius G c E ≤ R)
    (hGSL : S ≤ bhEntropy k G hbar c (schwarzschildRadius G c E)) :
    S ≤ 2 * π * k * R * E / (hbar * c) := by
  set r := schwarzschildRadius G c E
  refine hGSL.trans ?_
  rw [bhEntropy_eq_bekenstein hG.ne' hhbar.ne' hc.ne',
    schwarzschildEnergy_schwarzschildRadius hG.ne' hc.ne']
  have hpos : 0 < hbar * c := mul_pos hhbar hc
  rw [div_le_div_iff_of_pos_right hpos]
  have h2 : (0:ℝ) ≤ 2 * π * k := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfit h2) hE

end Phys

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

