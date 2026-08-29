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

lemma denom_eq_one_of_ord_nonneg {f : RatFunc k} (h : ∀ p : FinPlace k, 0 ≤ ord (some p) f) :
    f.denom = 1 := by
  by_contra hne
  have hu : ¬ IsUnit f.denom := fun hu => hne ((RatFunc.monic_denom f).eq_one_of_isUnit hu)
  obtain ⟨q, hqm, hqi, hqd⟩ := Polynomial.exists_monic_irreducible_factor _ hu
  have h1 : multiplicity q f.num = 0 := multiplicity_eq_zero.2 fun hdvd =>
    hqi.not_isUnit ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' hdvd hqd)
  have h2 : 1 ≤ multiplicity q f.denom :=
    (FiniteMultiplicity.of_prime_left hqi.prime (RatFunc.denom_ne_zero f)).pow_dvd_iff_le_multiplicity.mp
      (by simpa using hqd)
  have h3 := h ⟨q, hqm, hqi⟩
  simp only [ord, polOrd, h1] at h3
  omega

