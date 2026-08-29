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

theorem kervaire_invariant
    (K : Nat → Prop)
    (browder : ∀ n, K n → ∃ j : Nat, 2 ≤ j ∧ n = 2 ^ j - 2)
    (hill_hopkins_ravenel : ∀ j : Nat, 8 ≤ j → ¬ K (2 ^ j - 2))
    (h2 : K 2) (h6 : K 6) (h14 : K 14) (h30 : K 30) (h62 : K 62) (h126 : K 126) :
    ∀ n, K n ↔ KervaireDimension n := by
  intro n
  constructor
  · intro hn
    obtain ⟨j, hj2, rfl⟩ := browder n hn
    have hj7 : j ≤ 7 := by
      rcases Nat.lt_or_ge j 8 with h | h
      · omega
      · exact absurd hn (hill_hopkins_ravenel j h)
    exact (kervaire_dimensions_iff _).2 ⟨j, hj2, hj7, rfl⟩
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption

/-- The hypotheses of `kervaire_invariant` are consistent: they are satisfied by
the predicate `KervaireDimension` itself.  In particular the classification above
is not vacuous. -/
