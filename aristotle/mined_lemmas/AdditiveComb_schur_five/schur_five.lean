/-!
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AdditiveComb

/-- **Schur instance: `S(2) < 5`.**

Every 2-colouring `f` of `{1, 2, 3, 4, 5}` — encoded as `f : Fin 5 → Bool`, where the
index `i : Fin 5` stands for the integer `i.val + 1` — admits a monochromatic Schur
triple: there are `x, y, z ∈ {1, …, 5}` with `x + y = z` and `f x = f y = f z`.

The proof is exhaustive finite case analysis on the 32 colourings: in each case one of
the six Schur triples `(1,1,2)`, `(1,2,3)`, `(1,3,4)`, `(1,4,5)`, `(2,2,4)`, `(2,3,5)`
is monochromatic. -/

theorem schur_five (f : Fin 5 → Bool) :
    ∃ x y z : Fin 5,
      (x.val + 1) + (y.val + 1) = (z.val + 1) ∧ f x = f y ∧ f y = f z := by
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;> cases h3 : f 3 <;> cases h4 : f 4 <;>
    first
      | exact ⟨0, 0, 1, rfl, rfl, h0.trans h1.symm⟩
      | exact ⟨0, 1, 2, rfl, h0.trans h1.symm, h1.trans h2.symm⟩
      | exact ⟨0, 2, 3, rfl, h0.trans h2.symm, h2.trans h3.symm⟩
      | exact ⟨0, 3, 4, rfl, h0.trans h3.symm, h3.trans h4.symm⟩
      | exact ⟨1, 1, 3, rfl, rfl, h1.trans h3.symm⟩
      | exact ⟨1, 2, 4, rfl, h1.trans h2.symm, h2.trans h4.symm⟩

end AdditiveComb

import Mathlib
import RequestProject.SchurFive

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

#print axioms AdditiveComb.schur_five

