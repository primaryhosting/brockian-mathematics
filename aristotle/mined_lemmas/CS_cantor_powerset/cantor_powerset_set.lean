/-!
# Cantor Powerset
Category: Computer Science
Target: CS.cantor_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- **Cantor's theorem**: for every type `A`, no map from `A` to its powerset
`𝒫(A)` (represented by characteristic predicates `A → Prop`, which is definitionally
`Set A`) is surjective.

The header comment required for this file is a module docstring, which Lean requires
to precede any `import`; the statement and proof therefore use only Lean core notions.
A restatement in terms of Mathlib's `Set A` is given in
`RequestProject/CantorPowersetSet.lean`. -/

theorem cantor_powerset_set {A : Type u} (f : A → Set A) : ¬ Function.Surjective f :=
  cantor_powerset f

/-- **Cantor's theorem**, existential form: there is no surjection from `A` onto `𝒫(A)`. -/
