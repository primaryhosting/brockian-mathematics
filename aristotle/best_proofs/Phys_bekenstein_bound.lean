/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Statement: State the Bekenstein bound S ≤ 2πkRE/ℏc.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Statement: State the Bekenstein bound S ≤ 2πkRE/ℏc.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Real

/-- The Bekenstein bound value `2 π k R E / (ℏ c)`: the maximal entropy of a physical
system of radius `R` and total energy `E`, expressed with Boltzmann's constant `k`,
the reduced Planck constant `ℏ` and the speed of light `c`. -/
noncomputable def bekensteinBoundValue (k hbar c R E : ℝ) : ℝ :=
  2 * π * k * R * E / (hbar * c)

/-- The Bekenstein–Hawking entropy `k c³ A / (4 ℏ G)` of a black-hole horizon of area `A`. -/
noncomputable def bekensteinHawkingEntropy (k hbar G c A : ℝ) : ℝ :=
  k * c ^ 3 * A / (4 * hbar * G)

/-- The increase `8 π G E R / c⁴` of the horizon area of a black hole that absorbs a body of
energy `E` whose centre is lowered to proper distance `R` from the horizon. -/
noncomputable def horizonAreaIncrease (G c E R : ℝ) : ℝ :=
  8 * π * G * E * R / c ^ 4

/-- The Bekenstein–Hawking entropy associated with the horizon-area increase caused by
absorbing a body of energy `E` and radius `R` is exactly the Bekenstein bound value. -/
theorem bekensteinHawkingEntropy_horizonAreaIncrease
    (k hbar G c R E : ℝ) (hhbar : hbar ≠ 0) (hG : G ≠ 0) (hc : c ≠ 0) :
    bekensteinHawkingEntropy k hbar G c (horizonAreaIncrease G c E R)
      = bekensteinBoundValue k hbar c R E := by
  unfold bekensteinHawkingEntropy horizonAreaIncrease bekensteinBoundValue
  field_simp
  ring

/-- **The Bekenstein bound.**  For a physical system of radius `R` and total energy `E`,
the entropy `S` obeys `S ≤ 2 π k R E / (ℏ c)`.

The bound is obtained from the generalized second law of thermodynamics: if the system is
absorbed by a black hole, the resulting increase in the Bekenstein–Hawking horizon entropy
must be at least the entropy `S` that the system carried (hypothesis `hGSL`), and the horizon
area grows by `8 π G E R / c⁴` (Bekenstein's construction).  Combining these facts, and the
fact that the entropy of that area increase is exactly `2 π k R E / (ℏ c)`, gives the bound. -/
theorem bekenstein_bound
    (k hbar G c R E S : ℝ) (hhbar : hbar ≠ 0) (hG : G ≠ 0) (hc : c ≠ 0)
    (hGSL : S ≤ bekensteinHawkingEntropy k hbar G c (horizonAreaIncrease G c E R)) :
    S ≤ 2 * π * k * R * E / (hbar * c) := by
  have h := bekensteinHawkingEntropy_horizonAreaIncrease k hbar G c R E hhbar hG hc
  rw [h] at hGSL
  simpa [bekensteinBoundValue] using hGSL

/-- The Bekenstein bound is monotone in the energy of the system. -/
theorem bekensteinBoundValue_mono_energy
    (k hbar c R E₁ E₂ : ℝ) (hk : 0 ≤ k) (hR : 0 ≤ R) (hhbar : 0 < hbar) (hc : 0 < c)
    (h : E₁ ≤ E₂) :
    bekensteinBoundValue k hbar c R E₁ ≤ bekensteinBoundValue k hbar c R E₂ := by
  unfold bekensteinBoundValue
  have hkR : (0:ℝ) ≤ 2 * π * k * R := by positivity
  gcongr

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

