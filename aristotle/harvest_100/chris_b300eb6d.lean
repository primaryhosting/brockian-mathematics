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
noncomputable def bhEntropy (k G hbar c r : ℝ) : ℝ := π * k * c ^ 3 * r ^ 2 / (G * hbar)

/-- The energy `E = M c² = r c⁴ / (2G)` of a Schwarzschild black hole of horizon radius `r`. -/
noncomputable def schwarzschildEnergy (G c r : ℝ) : ℝ := r * c ^ 4 / (2 * G)

/-- The Schwarzschild radius `r = 2 G E / c⁴` associated with an energy `E`. -/
noncomputable def schwarzschildRadius (G c E : ℝ) : ℝ := 2 * G * E / c ^ 4

@[simp]
theorem schwarzschildEnergy_schwarzschildRadius {G c E : ℝ} (hG : G ≠ 0) (hc : c ≠ 0) :
    schwarzschildEnergy G c (schwarzschildRadius G c E) = E := by
  unfold schwarzschildEnergy schwarzschildRadius
  field_simp

/-- **Key lemma.** For a Schwarzschild black hole of horizon radius `r`, the
Bekenstein–Hawking entropy saturates the Bekenstein expression `2π k r E / (ℏ c)`,
where `E` is the black hole's energy. -/
theorem bhEntropy_eq_bekenstein {k G hbar c r : ℝ} (hG : G ≠ 0) (hhbar : hbar ≠ 0)
    (hc : c ≠ 0) :
    bhEntropy k G hbar c r = 2 * π * k * r * schwarzschildEnergy G c r / (hbar * c) := by
  unfold bhEntropy schwarzschildEnergy
  field_simp

/-- **The Bekenstein bound.** A physical system of energy `E ≥ 0` confined to a region of
radius `R` has entropy `S ≤ 2π k R E / (ℏ c)`.

The physical input is Susskind's collapse argument, encoded as hypotheses:
* `hfit` : the system is not already inside its own Schwarzschild radius, i.e.
  `2 G E / c⁴ ≤ R`;
* `hGSL` : by the second law of thermodynamics, collapsing the system into a black hole
  cannot decrease entropy, so `S` is at most the Bekenstein–Hawking entropy of the
  black hole of energy `E`.

From these, the bound follows from the key lemma
`bhEntropy_eq_bekenstein` together with monotonicity in the radius. -/
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

