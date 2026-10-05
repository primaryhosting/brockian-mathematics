/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
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

/-- The Unruh temperature `T = ℏ a / (2 π c k_B)` seen by an observer with proper
acceleration `a`, in terms of the reduced Planck constant `hbar`, the speed of light `c`
and Boltzmann's constant `kB`. -/

noncomputable def boseEinstein (hbar kB T omega : ℝ) : ℝ :=
  1 / (Real.exp (hbar * omega / (kB * T)) - 1)

/-- **The Unruh effect.**

For an observer undergoing uniform proper acceleration `a` (with `hbar, a, c, kB > 0`),
the Unruh temperature is
`T = ℏ a / (2 π c k_B)`,
and it is characterised by the following equivalent properties:

1. `T > 0`;
2. the thermal energy is `k_B T = ℏ a / (2 π c)`, i.e. `T` is the unique temperature whose
   thermal energy equals `ℏ a / (2 π c)`;
3. the Boltzmann factor at temperature `T` for a mode of angular frequency `ω` coincides with
   the Bogoliubov/Rindler factor `exp (-2 π c ω / a)` obtained from the periodicity of the
   Euclidean Rindler time, for every `ω`; equivalently `ℏ / (k_B T) = β` with
   `β = 2 π c / a` the Rindler period;
4. consequently the Rindler mode occupation numbers are exactly the Bose–Einstein
   occupation numbers at temperature `T`.
-/
