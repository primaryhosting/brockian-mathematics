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

lemma exists_principal (D : Divisor k) :
    ∃ g : RatFunc k, g ≠ 0 ∧ D - divisorOf g = Finsupp.single none (degDiv D) := by
  induction D using Finsupp.induction with
  | zero => exact ⟨1, one_ne_zero' (RatFunc k), by simp [divisorOf_one]⟩
  | single_add a b F _ _ ih =>
    obtain ⟨g', hg', hF⟩ := ih
    obtain ⟨h, hh, hdh⟩ := exists_base a
    refine ⟨h ^ b * g', mul_ne_zero (zpow_ne_zero _ hh) hg', ?_⟩
    rw [divisorOf_mul (zpow_ne_zero _ hh) hg', divisorOf_zpow hh, hdh, degDiv_add,
      degDiv_single, smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul,
      smul_eq_mul, mul_one]
    have key : Finsupp.single a b + F -
        (Finsupp.single a b - Finsupp.single (none : Place k) (b * placeDeg a) + divisorOf g')
        = (F - divisorOf g') + Finsupp.single (none : Place k) (b * placeDeg a) := by abel
    rw [key, hF, ← Finsupp.single_add, add_comm]

/-! ### The Riemann–Roch space of a multiple of the point at infinity -/

/-- The inclusion of polynomials into rational functions, as a `k`-linear map. -/
