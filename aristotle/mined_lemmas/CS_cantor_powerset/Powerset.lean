/-!
# Cantor Powerset
Category: Computer Science
Target: CS.cantor_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The powerset of a type, represented by characteristic predicates:
`S : Powerset A` stands for the subset `{a | S a}` of `A`. -/

def Powerset (A : Type u) : Type u := A → Prop

/-- **Cantor's theorem**: there is no surjection from a type `A` onto its powerset `𝒫(A)`.

The powerset is represented here as `A → Prop` (characteristic predicates), which is
definitionally Mathlib's `Set A`; see `CS.cantor_powerset_set` in
`RequestProject.CantorPowersetSet` for the `Set`-valued restatement, which also cites
Mathlib's own `Function.cantor_surjective`.

Proof: the diagonal subset `{a | ¬ f a a}` is not in the range of `f`. -/
