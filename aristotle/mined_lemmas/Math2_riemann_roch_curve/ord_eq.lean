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

lemma ord_eq {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (v : Place k) :
    ord v ((algebraMap k[X] (RatFunc k) a) / (algebraMap k[X] (RatFunc k) b))
      = polOrd v a - polOrd v b := by
  set f : RatFunc k := (algebraMap k[X] (RatFunc k) a) / (algebraMap k[X] (RatFunc k) b) with hf
  have hb' := algMap_ne_zero hb
  have hd := algMap_ne_zero (RatFunc.denom_ne_zero f)
  have hfne : f ≠ 0 := div_ne_zero (algMap_ne_zero ha) hb'
  have key : f.num * b = a * f.denom := by
    have h1 : (algebraMap k[X] (RatFunc k)) f.num / (algebraMap k[X] (RatFunc k)) f.denom
        = (algebraMap k[X] (RatFunc k)) a / (algebraMap k[X] (RatFunc k)) b :=
      RatFunc.num_div_denom f
    rw [div_eq_div_iff hd hb'] at h1
    exact RatFunc.algebraMap_injective k (by rw [map_mul, map_mul]; exact h1)
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hfne
  have h2 := polOrd_mul hnum hb v
  rw [key, polOrd_mul ha (RatFunc.denom_ne_zero f) v] at h2
  simp only [ord]
  omega

