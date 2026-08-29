import Mathlib

/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
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

/-- The Bekenstein bound value `2 π k R E / (ℏ c)`: the maximal entropy that can be
contained in a region of radius `R` enclosing total energy `E`. -/
noncomputable def bekensteinBoundValue (k hbar c R E : ℝ) : ℝ :=
  2 * Real.pi * k * R * E / (hbar * c)

/-- Schwarzschild radius `2 G M / c²` of a body of mass `M`. -/
noncomputable def schwarzschildRadius (G c M : ℝ) : ℝ := 2 * G * M / c ^ 2

/-- Hawking temperature `ℏ c³ / (8 π G M k)` of a Schwarzschild black hole of mass `M`. -/
noncomputable def hawkingTemperature (k hbar c G M : ℝ) : ℝ :=
  hbar * c ^ 3 / (8 * Real.pi * G * M * k)

/-- Bekenstein–Hawking entropy `k c³ A / (4 G ℏ)` of a Schwarzschild black hole of mass `M`,
written out with `A = 4 π (2GM/c²)²`, i.e. `4 π k G M² / (ℏ c)`. -/
noncomputable def bekensteinHawkingEntropy (k hbar c G M : ℝ) : ℝ :=
  4 * Real.pi * k * G * M ^ 2 / (hbar * c)

/-- Near-horizon redshift factor `R c² / (4 G M)` at proper distance `R` above the horizon of a
Schwarzschild black hole of mass `M`. -/
noncomputable def nearHorizonRedshift (c G M R : ℝ) : ℝ := R * c ^ 2 / (4 * G * M)

/-- Energy actually delivered to the horizon when a body of rest-frame energy `E` is lowered
quasi-statically (Geroch process) to proper distance `R` above the horizon: the energy is
redshifted by `nearHorizonRedshift`. -/
noncomputable def deliveredEnergy (c G M R E : ℝ) : ℝ := E * nearHorizonRedshift c G M R

/-- Entropy gained by the horizon when it absorbs energy `ΔE` at temperature `T`:
the Clausius relation `ΔS = ΔE / T`. -/
noncomputable def horizonEntropyIncrease (T dE : ℝ) : ℝ := dE / T

/-- **Bekenstein–Hawking entropy saturates the Bekenstein bound.**
For a Schwarzschild black hole of mass `M`, radius `R = 2GM/c²` and energy `E = M c²`,
the entropy `4 π k G M² / (ℏ c)` equals exactly `2 π k R E / (ℏ c)`. -/
theorem bekensteinHawking_saturates (k hbar c G M : ℝ) (hc : c ≠ 0) :
    bekensteinHawkingEntropy k hbar c G M
      = bekensteinBoundValue k hbar c (schwarzschildRadius G c M) (M * c ^ 2) := by
  unfold bekensteinHawkingEntropy bekensteinBoundValue schwarzschildRadius
  field_simp
  ring

/-- **Geroch process computation.**
Lowering a body of energy `E` and radius `R` to just outside the horizon of a Schwarzschild
black hole of mass `M` and letting it fall in raises the horizon entropy by exactly
`2 π k R E / (ℏ c)`, independently of the black hole mass `M`. -/
theorem geroch_entropyIncrease_eq_bekensteinBoundValue
    (k hbar c G M R E : ℝ) (hk : k ≠ 0) (hhbar : hbar ≠ 0) (hc : c ≠ 0)
    (hG : G ≠ 0) (hM : M ≠ 0) :
    horizonEntropyIncrease (hawkingTemperature k hbar c G M) (deliveredEnergy c G M R E)
      = bekensteinBoundValue k hbar c R E := by
  unfold horizonEntropyIncrease hawkingTemperature deliveredEnergy nearHorizonRedshift
    bekensteinBoundValue
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **The Bekenstein bound.**

A body of total energy `E` fitting inside a sphere of radius `R` carries entropy at most
`S ≤ 2 π k R E / (ℏ c)`.

The physical input is the generalized second law (`hGSL`): when the body is lowered
quasi-statically into a Schwarzschild black hole of mass `M` (Geroch process) and dropped in
from proper distance `R` above the horizon, its entropy `S` is destroyed, so the horizon
entropy must increase by at least `S`. The remaining content of the theorem is the exact
computation of that horizon entropy increase, which equals `2 π k R E / (ℏ c)` for every
black hole mass `M`. -/
theorem bekenstein_bound
    (k hbar c G M R E S : ℝ) (hk : 0 < k) (hhbar : 0 < hbar) (hc : 0 < c)
    (hG : 0 < G) (hM : 0 < M)
    (hGSL : S ≤ horizonEntropyIncrease (hawkingTemperature k hbar c G M)
              (deliveredEnergy c G M R E)) :
    S ≤ 2 * Real.pi * k * R * E / (hbar * c) := by
  have h := geroch_entropyIncrease_eq_bekensteinBoundValue k hbar c G M R E
    hk.ne' hhbar.ne' hc.ne' hG.ne' hM.ne'
  rw [h] at hGSL
  simpa [bekensteinBoundValue] using hGSL

end Phys

