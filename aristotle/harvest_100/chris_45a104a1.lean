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

/-- **Schur instance `S(2) < 5`.** Every 2-colouring `f` of `{1, …, 5}`
(encoded as a function `Fin 5 → Bool`, where the index `i` stands for the
number `i + 1`) admits a monochromatic Schur triple: elements `x, y, z` with
`(x+1) + (y+1) = (z+1)` and `f x = f y = f z`. Proved by finite case analysis. -/
theorem schur_five (f : Fin 5 → Bool) :
    ∃ x y z : Fin 5,
      ((x : ℕ) + 1) + ((y : ℕ) + 1) = ((z : ℕ) + 1) ∧ f x = f y ∧ f y = f z := by
  revert f
  decide

end AdditiveComb

