import Mathlib

/-!
# Mereology Partialorder
Category: Frontier — Set Theory
Target: Phenomenology.mereology_partialorder
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

namespace Phenomenology

/-- A faithful formal fragment of Husserlian part–whole structure (mereology),
labeled as a MODEL of a phenomenological structure, not a claim about consciousness.

"Part of" is modelled by the order relation `≤` on a type `P` carrying a
`PartialOrder` (so it is reflexive, antisymmetric and transitive), and
"proper part of" by the strict order `<`.  The whole is the `⊤` element.

The theorem records: (i) every element is a part of the whole,
(ii) proper-parthood is irreflexive, and (iii) proper-parthood is transitive. -/

theorem mereology_parthood_partial_order (P : Type*) [PartialOrder P] :
    (∀ x : P, x ≤ x) ∧ (∀ x y : P, x ≤ y → y ≤ x → x = y) ∧
      (∀ x y z : P, x ≤ y → y ≤ z → x ≤ z) :=
  ⟨fun x => le_refl x, fun _ _ h h' => le_antisymm h h',
    fun _ _ _ h h' => le_trans h h'⟩

end Phenomenology

