/-
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

set_option grind.warning false

namespace Phenomenology

/--
A faithful formal fragment of Husserlian part–whole structure (mereology), stated as a
MODEL and not as a claim about consciousness.

`part-of` is modelled by the partial order `≤` on a type `P` (reflexive, antisymmetric,
transitive), `proper-part-of` by the strict order `<`, and `the whole` by a top element.

The theorem records three facts:
* every element is a part of the whole (`x ≤ ⊤`);
* proper-part-of is irreflexive (`¬ x < x`);
* proper-part-of is transitive (`x < y → y < z → x < z`).
-/
theorem mereology_partialorder (P : Type*) [PartialOrder P] [OrderTop P] :
    (∀ x : P, x ≤ (⊤ : P)) ∧
    (∀ x : P, ¬ x < x) ∧
    (∀ x y z : P, x < y → y < z → x < z) := by
  refine ⟨fun x => le_top, fun x => lt_irrefl x, fun x y z hxy hyz => lt_trans hxy hyz⟩

end Phenomenology

