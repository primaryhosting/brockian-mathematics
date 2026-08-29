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

lemma ord_add_ge {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) (v : Place k) :
    min (ord v f) (ord v g) ≤ ord v (f + g) := by
  set a : k[X] := f.num * g.denom + g.num * f.denom with ha
  have hden : f.denom * g.denom ≠ 0 :=
    mul_ne_zero (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)
  have hrep : f + g = (algebraMap k[X] (RatFunc k) a)
      / (algebraMap k[X] (RatFunc k) (f.denom * g.denom)) := by
    have h1 := algMap_ne_zero (RatFunc.denom_ne_zero f)
    have h2 := algMap_ne_zero (RatFunc.denom_ne_zero g)
    rw [ha, map_add, map_mul, map_mul, map_mul, eq_div_iff (mul_ne_zero h1 h2)]
    nth_rewrite 1 [← RatFunc.num_div_denom f, ← RatFunc.num_div_denom g]
    field_simp
  have hane : a ≠ 0 := by
    intro h
    apply hfg
    rw [hrep, h, map_zero, zero_div]
  rw [hrep, ord_eq hane hden v]
  have h1 : polOrd v (f.num * g.denom) = polOrd v f.num + polOrd v g.denom :=
    polOrd_mul (RatFunc.num_ne_zero hf) (RatFunc.denom_ne_zero g) v
  have h2 : polOrd v (g.num * f.denom) = polOrd v g.num + polOrd v f.denom :=
    polOrd_mul (RatFunc.num_ne_zero hg) (RatFunc.denom_ne_zero f) v
  have h3 : polOrd v (f.denom * g.denom) = polOrd v f.denom + polOrd v g.denom :=
    polOrd_mul (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g) v
  have h4 := polOrd_add_ge (x := f.num * g.denom) (y := g.num * f.denom) (by rwa [← ha]) v
  rw [← ha] at h4
  simp only [ord]
  rw [h3]
  rw [h1, h2] at h4
  omega

/-- A nonzero rational function has nonzero order at only finitely many places. -/
