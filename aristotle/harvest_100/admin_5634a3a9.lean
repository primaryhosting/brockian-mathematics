/-!
# Mereology Partialorder
Category: Frontier — Set Theory
Target: Phenomenology.mereology_partialorder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phenomenology

/-- A faithful formal fragment of Husserlian part-whole mereology (a MODEL, not a
claim about consciousness): `part-of` is modelled by the order `≤` of a partial order
on `P`, and `proper-part-of` by the strict order `<`.

We prove:
* the whole (`⊤`, when present) has every element as a part (`x ≤ ⊤`);
* proper-part-of is irreflexive (`¬ (x < x)`);
* proper-part-of is transitive (`x < y → y < z → x < z`).

Each component is closed by an existing Mathlib lemma: `le_top`, `lt_irrefl`
and `lt_trans`. -/
theorem mereology_partialorder (P : Type*) [PartialOrder P] [OrderTop P] :
    (∀ x : P, x ≤ (⊤ : P)) ∧ (∀ x : P, ¬ (x < x)) ∧
      (∀ x y z : P, x < y → y < z → x < z) :=
  ⟨fun x => le_top, fun x => lt_irrefl x, fun _ _ _ hxy hyz => lt_trans hxy hyz⟩

end Phenomenology

