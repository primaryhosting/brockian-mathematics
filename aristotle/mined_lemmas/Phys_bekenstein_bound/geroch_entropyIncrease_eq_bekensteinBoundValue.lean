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
