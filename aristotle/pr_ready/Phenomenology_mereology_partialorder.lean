/-!
# Mereology Partialorder
Category: Frontier — Set Theory
Target: Phenomenology.mereology_partialorder
Statement: A faithful formal fragment of Husserlian part-whole (mereology): model 'part-of' as a partial order on a type P (reflexive, antisymmetric, transitive) and prove that proper-part-of (strict order) is irreflexive and transitive, and that the whole (a Top element, if present) has every element as a part. Concretely: given [PartialOrder P] [OrderTop P], prove for all x : P, x <= (Top : P), and for ...
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Phenomenology

/--
A faithful formal fragment of Husserlian part-whole structure (mereology), stated as a MODEL
of a phenomenological structure, not as a claim about consciousness.

`part-of` is modelled by the partial order `≤` on a type `P` (reflexive, antisymmetric,
transitive), and `proper-part-of` by the strict order `<`. The theorem records that:

* the whole (the `⊤` element, when present) has every element as a part;
* proper-part-of is irreflexive;
* proper-part-of is transitive.
-/
theorem mereology_partialorder (P : Type*) [PartialOrder P] [OrderTop P] :
    (∀ x : P, x ≤ (⊤ : P)) ∧ (∀ x : P, ¬ (x < x)) ∧
      (∀ x y z : P, x < y → y < z → x < z) :=
  ⟨fun _ => le_top, fun x => lt_irrefl x, fun _ _ _ hxy hyz => lt_trans hxy hyz⟩

end Phenomenology

