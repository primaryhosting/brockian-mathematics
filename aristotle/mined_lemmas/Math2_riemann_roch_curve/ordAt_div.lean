import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
## Scope and setup

We formalise the Riemann–Roch theorem for the projective line `ℙ¹` over an algebraically
closed field `k`, a smooth projective curve, with everything built from scratch:

* the places of `ℙ¹` are the points `a : k` of the affine line together with the point at
  infinity, and the associated discrete valuations are `ordAt a` and `ordInf`;
* a divisor is a finitely supported family of integers on the affine points together with a
  coefficient at infinity, and `Divisor.deg` is its degree;
* `RRSpace D` is the Riemann-Roch space `L(D) = {f : div f + D ≥ 0}` and
  `ell D = ℓ(D) = dim_k L(D)`;
* `canonicalDivisor k` is the divisor `-2·∞` of the differential `dt`, and the genus is
  defined intrinsically as `genus k = ℓ(K)`.

The main theorem `Math2.riemann_roch_curve` states `ℓ(D) - ℓ(K - D) = deg D + 1 - g`.
It is deduced from the computation `Math2.ell_eq : ℓ(D) = max (deg D + 1) 0`, which is proved
by exhibiting an explicit `k`-linear isomorphism between `L(D)` and the space of polynomials
of degree at most `deg D`.
-/

namespace Math2

open Polynomial

variable {k : Type*} [Field k]

/-! ## Orders of vanishing (the discrete valuations of `ℙ¹`) -/

/-- The order of vanishing at the point `a` of the affine line, of a rational function `f`. -/

theorem ordAt_div (a : k) {P Q : k[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ordAt a (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q)
      = (P.rootMultiplicity a : ℤ) - (Q.rootMultiplicity a : ℤ) := by
  set f : RatFunc k := algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q with hf
  have hf0 : f ≠ 0 := by
    simp [hf, RatFunc.algebraMap_ne_zero hP, RatFunc.algebraMap_ne_zero hQ]
  have hcross : f.num * Q = P * f.denom := by
    have h1 : (algebraMap k[X] (RatFunc k)) (f.num * Q)
        = (algebraMap k[X] (RatFunc k)) (P * f.denom) := by
      push_cast [map_mul]
      rw [← div_eq_div_iff (RatFunc.algebraMap_ne_zero f.denom_ne_zero)
        (RatFunc.algebraMap_ne_zero hQ), RatFunc.num_div_denom]
    exact IsFractionRing.injective k[X] (RatFunc k) h1
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf0
  have h2 := congrArg (fun p => Polynomial.rootMultiplicity a p) hcross
  simp only [Polynomial.rootMultiplicity_mul (mul_ne_zero hnum hQ),
    Polynomial.rootMultiplicity_mul (mul_ne_zero hP f.denom_ne_zero)] at h2
  simp only [ordAt]
  omega

