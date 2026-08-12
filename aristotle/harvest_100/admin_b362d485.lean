import Mathlib

/-!
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
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

namespace AdditiveComb

/-- **Schur's instance `S(2) < 5`.**

Every `2`-colouring `f : Fin 5 → Bool` of the set `{1, 2, 3, 4, 5}` (the index `i : Fin 5`
representing the integer `i + 1`) admits a monochromatic Schur triple: there are
`x, y, z` in `{1, …, 5}` with `x + y = z` and `f x = f y = f z`
(the values `x` and `y` are allowed to coincide).

Proved by exhaustive finite case analysis over the `32` colourings. -/
theorem schur_five (f : Fin 5 → Bool) :
    ∃ x y z : Fin 5, ((x : ℕ) + 1) + ((y : ℕ) + 1) = (z : ℕ) + 1 ∧ f x = f y ∧ f y = f z := by
  revert f
  decide

end AdditiveComb

