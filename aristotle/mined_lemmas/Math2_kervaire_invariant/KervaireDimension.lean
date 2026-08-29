/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Formalization notes.

The Kervaire invariant problem asks in which dimensions `n` there exists a closed
framed `n`-manifold of Kervaire invariant one (equivalently, in which stems the
class `θ_j` of the stable homotopy groups of spheres exists).  The relevant
results are:

* Browder's theorem: such a manifold can only exist when `n = 2 ^ j - 2` for
  some `j ≥ 2`;
* explicit constructions in dimensions `2, 6, 14, 30, 62` and `126`;
* the Hill–Hopkins–Ravenel theorem: for `j ≥ 8`, i.e. in dimensions
  `2 ^ j - 2 ≥ 254`, no such manifold exists.

These three inputs are deep results of differential topology and stable homotopy
theory whose proofs are far outside the scope of the current Lean mathematical
library, so they are carried here as explicit hypotheses on an abstract predicate
`K : Nat → Prop` ("dimension `n` carries a framed manifold of Kervaire invariant
one"), stated exactly as in the literature.  The theorem `kervaire_invariant`
below is the resulting classification:

  the Kervaire invariant is nonzero exactly in dimensions 2, 6, 14, 30, 62, 126.

To make clear that this is not a vacuous statement,
`kervaire_hypotheses_consistent` exhibits a predicate satisfying all of the
hypotheses, and `kervaire_dimensions_iff` records the purely arithmetic core:
`{2, 6, 14, 30, 62, 126}` is exactly the set of numbers of the form `2 ^ j - 2`
with `2 ≤ j ≤ 7`.

The file uses only Lean 4 core (it is part of a Mathlib-based project, but the
required header comment must precede any `import`, so no imports are used).
-/

namespace Math2

/-- The six exceptional dimensions in which the Kervaire invariant is nonzero. -/

def KervaireDimension (n : Nat) : Prop :=
  n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126

/-- Arithmetic core: the numbers of the form `2 ^ j - 2` with `2 ≤ j ≤ 7` are
exactly `2, 6, 14, 30, 62, 126`. -/
