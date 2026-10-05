/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

This file develops, from scratch, the divisor theory of the smooth projective curve `ℙ¹`
over an arbitrary field `k`, through its function field `k(X) = RatFunc k`, and proves the
Riemann–Roch theorem for it:

  `ℓ(D) - ℓ(K - D) = deg D + 1 - g`.

Nothing is assumed: all of the following are defined here and all statements are proved.

* `Place k`: the closed points of `ℙ¹`, namely the monic irreducible polynomials
  (finite points) together with the point at infinity.
* `placeDeg`, `Divisor k`, `degDiv`: degrees of points, divisors and their degrees.
* `ord v f`: the order of vanishing of a rational function at a closed point, and
  `divisorOf f` the principal divisor of `f`.
* `RRSpace D` (`= L(D)`) and `ell D` (`= ℓ(D) = dim_k L(D)`).
* `canonicalDivisor k = -2·[∞]`, the divisor of the differential `dX`, and
  `genus k = ℓ(K)`, the dimension of the space of regular differentials.

The main results are `Math2.riemann_roch_curve`, together with `Math2.ell_eq`
(`ℓ(D) = max (deg D + 1) 0`), `Math2.genus_eq_zero` (`ℙ¹` has genus `0`),
`Math2.degDiv_canonical_eq` (`deg K = 2g - 2`) and `Math2.degDiv_divisorOf` (a principal
divisor has degree `0`).

The scope is the projective line: Mathlib has no theory of divisors, linear systems or
Serre duality for general curves, so the curve treated here is `ℙ¹`, for which the whole
theory is built by hand.
-/

namespace Math2

open Polynomial UniqueFactorizationMonoid

variable {k : Type*} [Field k]

/-- A finite closed point of the projective line `ℙ¹` over `k`: a monic irreducible
polynomial in `k[X]`. -/
abbrev FinPlace (k : Type*) [Field k] : Type _ := {p : k[X] // p.Monic ∧ Irreducible p}

/-- The closed points of `ℙ¹` over `k`: the finite places together with the point at
infinity, represented by `none`. -/
abbrev Place (k : Type*) [Field k] : Type _ := Option (FinPlace k)

/-- The degree of a closed point: `1` at infinity, `deg p` at a finite place `p`. -/

lemma polOrd_add_ge {x y : k[X]} (hxy : x + y ≠ 0) (v : Place k) :
    min (polOrd v x) (polOrd v y) ≤ polOrd v (x + y) := by
  cases v with
  | none =>
    simp only [polOrd, min_le_iff, neg_le_neg_iff]
    have := Polynomial.natDegree_add_le x y
    rcases le_total x.natDegree y.natDegree with h | h
    · right; exact_mod_cast le_trans (by exact_mod_cast this) (by simpa using h)
    · left; exact_mod_cast le_trans (by exact_mod_cast this) (by simpa using h)
  | some p =>
    simp only [polOrd, ← Nat.cast_min, Nat.cast_le]
    have hdx : p.1 ^ (min (multiplicity p.1 x) (multiplicity p.1 y)) ∣ x :=
      dvd_trans (pow_dvd_pow _ (min_le_left _ _)) (pow_multiplicity_dvd _ _)
    have hdy : p.1 ^ (min (multiplicity p.1 x) (multiplicity p.1 y)) ∣ y :=
      dvd_trans (pow_dvd_pow _ (min_le_right _ _)) (pow_multiplicity_dvd _ _)
    exact (FiniteMultiplicity.of_prime_left p.prime hxy).pow_dvd_iff_le_multiplicity.mp
      (dvd_add hdx hdy)

/-- `ord` may be computed from any representation of `f` as a quotient of polynomials. -/
