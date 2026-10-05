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

/-- A formal MODEL of a fragment of Husserlian part-whole theory (mereology).

`part-of` is modelled as a partial order `≤` on a type `P` (reflexive, antisymmetric,
transitive), `proper-part-of` as the associated strict order `<`, and `the whole` as a
top element `⊤` (assumed to exist via `[OrderTop P]`).

The statement records three structural facts of this model:
* every element is a part of the whole (`x ≤ ⊤`, Mathlib: `le_top`);
* proper-part-of is irreflexive (`¬ x < x`, Mathlib: `lt_irrefl`);
* proper-part-of is transitive (`x < y → y < z → x < z`, Mathlib: `lt_trans`).

This is a mathematical model of a phenomenological structure, not a claim about
consciousness. -/
theorem mereology_partialorder (P : Type*) [PartialOrder P] [OrderTop P] :
    (∀ x : P, x ≤ (⊤ : P)) ∧ (∀ x : P, ¬ x < x) ∧
      (∀ x y z : P, x < y → y < z → x < z) :=
  ⟨fun _ => le_top, fun x => lt_irrefl x, fun _ _ _ hxy hyz => lt_trans hxy hyz⟩

end Phenomenology

#print axioms Phenomenology.mereology_partialorder

