/-!
# Cantor Powerset
Category: Computer Science
Target: CS.cantor_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment above is a module docstring, which Lean requires
-- to be the first command in the file; therefore this file carries no `import` line.
-- Nothing beyond Lean core is needed: the powerset of `A` is represented by its
-- characteristic predicates `A → Prop`, which is definitionally Mathlib's `Set A`.
-- The file `RequestProject/CantorPowersetSet.lean` restates the result using
-- Mathlib's `Set A` and `_root_.Set.powerset`.

namespace CS

/-- **Cantor's theorem**: for any type `A`, no map `f : A → 𝒫(A)` is surjective,
where the powerset `𝒫(A)` is represented by characteristic predicates `A → Prop`
(definitionally Mathlib's `Set A`). -/

theorem cantor_powerset_univ {A : Type u} (f : A → Set A) :
    ¬ ∀ s ∈ (Set.univ : Set A).powerset, ∃ a, f a = s := by
  intro h
  exact cantor_powerset_set f fun s => h s (by simp)

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

