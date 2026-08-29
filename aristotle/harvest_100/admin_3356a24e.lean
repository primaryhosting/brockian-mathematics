import Mathlib
/-!
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AdditiveComb

/-- **Schur instance (S(2) < 5).** For every 2-colouring `f` of `{1, 2, 3, 4, 5}`
(encoded as `Fin 5`, with the element `i : Fin 5` representing the number `i + 1`),
there exist `x`, `y`, `z` in `{1, …, 5}` with `x + y = z` which all receive the same
colour, i.e. a monochromatic Schur triple. -/
theorem schur_five (f : Fin 5 → Bool) :
    ∃ x y z : Fin 5,
      (x.val + 1) + (y.val + 1) = (z.val + 1) ∧ f x = f y ∧ f y = f z := by
  revert f
  decide +kernel

end AdditiveComb

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

