/-!
# Psi Cubic Eq One Of Small
Category: A Assembly
Target: Zeta23Scaffold.psiCubic_eq_one_of_small
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Scaffold

/-- The cubic weight `psi(m) = m/2 + (2·m^2 - m^3)/18 + (4/9)·[m = 1]`
of preprint SS7.5(g). -/
def psiCubic (m : Nat) : Rat :=
  (m : Rat) / 2 + (2 * (m : Rat) ^ 2 - (m : Rat) ^ 3) / 18 + (if m = 1 then 4 / 9 else 0)

unseal Rat.add Rat.mul Rat.sub Rat.inv Nat.gcd in
/-- The cubic weight attains the value `1` at `m = 1`, `m = 2` and `m = 3`. -/
theorem psiCubic_eq_one_of_small :
    psiCubic 1 = 1 ∧ psiCubic 2 = 1 ∧ psiCubic 3 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Zeta23Scaffold

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

