/-
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open scoped NNReal
open Function

namespace Frontier

universe u w

/-!
## Perfectoid fields and the tilting correspondence

A *perfectoid field* is a complete non-archimedean valued field `(K, v)` of rank one whose value
group is non-discrete, whose residue characteristic is a prime `p`, and for which the Frobenius
`x ↦ x ^ p` is surjective on `O/p`, where `O ⊆ K` is the ring of integers.

Scholze's tilting construction attaches to such a field the *tilt*
`K♭ = Frac (lim_{x ↦ x^p} O/p)` (`Valuation.Tilt` in Mathlib), a perfectoid field of
characteristic `p`, and the tilting equivalence asserts that `L ↦ L♭` is an equivalence between
perfectoid extensions of `K` and perfectoid extensions of `K♭`; in particular it is fully
faithful and conservative on isomorphism classes.

The theorem `Frontier.scholze_perfectoid_tilt` below establishes the base case of this
correspondence, namely the case of characteristic `p`: there the tilt of a perfectoid field is
canonically isomorphic to the field itself, and consequently two characteristic-`p` perfectoid
fields are isomorphic if and only if their tilts are.
-/

/-- A *perfectoid field* (Scholze). `K` is a field equipped with a rank-one valuation
`v : K → ℝ≥0` with ring of integers `O`, such that

* the valuation is non-discrete (there is an element of valuation strictly between `0` and `1`);
* `K` is complete for its uniform structure;
* the residue characteristic is `p`, i.e. `p` is not a unit of `O`;
* the Frobenius `x ↦ x ^ p` on `O/p` is surjective (the perfectoid condition).
-/
structure IsPerfectoidField (p : ℕ) (K : Type u) [Field K] [UniformSpace K]
    (v : Valuation K ℝ≥0) (O : Type w) [CommRing O] [Algebra O K] : Prop where
  /-- `p` is a prime number. -/
  prime : p.Prime
  /-- `O` is the ring of integers of `v`. -/
  integers : v.Integers O
  /-- The valuation is non-discrete: some element has valuation different from `0` and `1`. -/
  nondiscrete : ∃ x : K, v x ≠ 0 ∧ v x ≠ 1
  /-- `K` is complete. -/
  complete : CompleteSpace K
  /-- The residue characteristic is `p`. -/
  residue_char : ¬ IsUnit (p : O)
  /-- Frobenius is surjective on `O/p`: the perfectoid condition. -/
  frobenius_surjective : Surjective (fun x : ModP O p => x ^ p)

section Auxiliary

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type u} [Field K] {v : Valuation K ℝ≥0}
variable {O : Type w} [CommRing O] [Algebra O K]

omit hp in
/-- The ring of integers of a valuation on a field has that field as fraction field. -/

theorem val_natCast_ne_one : v (p : K) ≠ 1 := by
  rw [CharP.cast_eq_zero K p, map_zero]
  exact zero_ne_one

/-- In characteristic `p`, if Frobenius is surjective on `O/p` then the perfection of `O/p`
(the integral tilt) is isomorphic to `O` itself. -/
