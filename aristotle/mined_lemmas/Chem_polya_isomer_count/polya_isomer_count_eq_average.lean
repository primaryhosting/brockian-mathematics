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

import Mathlib

/-!
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MulAction

namespace Chem

attribute [local instance] arrowAction

variable {G P C : Type*} [Group G] [MulAction G P]

/-- The subgroup of symmetries that leave a given substitution pattern (colouring) `f`
unchanged pointwise, i.e. `f (h • p) = f p` for all positions `p`. -/

theorem polya_isomer_count_eq_average [Fintype G] [Finite P] [Finite C] :
    Nat.card (orbitRel.Quotient G (P → C))
      = (∑ g : G, Nat.card C ^ cycleCount P g) / Nat.card G := by
  have hG : 0 < Nat.card G := Nat.card_pos
  rw [← polya_isomer_count (P := P) (C := C), Nat.mul_div_cancel _ hG]

end Chem

