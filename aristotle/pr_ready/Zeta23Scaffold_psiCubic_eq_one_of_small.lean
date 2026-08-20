/-!
# Psi Cubic Eq One Of Small
Category: A Assembly
Target: Zeta23Scaffold.psiCubic_eq_one_of_small
Statement: The cubic weight psi(m) = m/2 + (2m^2 - m^3)/18 + (4/9)*[m=1] of preprint SS7.5(g) attains equality psi(m)=1 at m = 1, 2, 3.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The cubic weight of preprint SS7.5(g):
`psi(m) = m/2 + (2*m^2 - m^3)/18 + (4/9)*[m = 1]`. -/
def psiCubic (m : Nat) : Rat :=
  (m : Rat) / 2 + (2 * (m : Rat) ^ 2 - (m : Rat) ^ 3) / 18 + (if m = 1 then 4 / 9 else 0)

/-- The cubic weight `psiCubic` attains the value `1` at `m = 1, 2, 3`. -/
theorem psiCubic_eq_one_of_small :
    psiCubic 1 = 1 ∧ psiCubic 2 = 1 ∧ psiCubic 3 = 1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

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

