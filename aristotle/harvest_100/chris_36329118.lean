/-
# Cantor Powerset
Category: Computer Science
Target: CS.cantor_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Cantor Powerset
Category: Computer Science
Target: CS.cantor_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- **Cantor's theorem**: for any type `A`, no function `f : A → Set A` is surjective,
i.e. there is no surjection from `A` onto its powerset `𝒫(A)`.
This is exactly Mathlib's `Function.cantor_surjective`. -/
theorem cantor_powerset {A : Type*} (f : A → Set A) : ¬ Function.Surjective f :=
  Function.cantor_surjective f

/-- Restatement: there does not exist a surjection from `A` onto `Set A`. -/
theorem not_exists_surjective_powerset {A : Type*} :
    ¬ ∃ f : A → Set A, Function.Surjective f := by
  rintro ⟨f, hf⟩
  exact cantor_powerset f hf

end CS

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

