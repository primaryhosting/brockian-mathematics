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

theorem ordAt_smul (a : k) {c : k} (hc : c ≠ 0) (f : RatFunc k) :
    ordAt a (c • f) = ordAt a f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hCc : (RatFunc.C c : RatFunc k) ≠ 0 := by
    simpa using hc
  have h0 : ordAt a (RatFunc.C c : RatFunc k) = 0 := by
    rw [← RatFunc.algebraMap_C, ordAt_polynomial]
    rw [Polynomial.rootMultiplicity_eq_zero (by simpa using hc)]
    simp
  rw [RatFunc.smul_eq_C_mul, ordAt_mul a hCc hf, h0, zero_add]

