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

theorem le_ordAt_add (a : k) {f g : RatFunc k} {n : ℤ} (hfg : f + g ≠ 0)
    (hf : n ≤ ordAt a f) (hg : n ≤ ordAt a g) : n ≤ ordAt a (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simpa using hg
  rcases eq_or_ne g 0 with rfl | hg0
  · simpa using hf
  have hN : f.num * g.denom + f.denom * g.num ≠ 0 :=
    RatFunc.num_mul_denom_add_denom_mul_num_ne_zero hfg
  have key : f + g = algebraMap k[X] (RatFunc k) (f.num * g.denom + f.denom * g.num)
      / algebraMap k[X] (RatFunc k) (f.denom * g.denom) := by
    conv_lhs => rw [← RatFunc.num_div_denom f, ← RatFunc.num_div_denom g]
    rw [div_add_div _ _ (RatFunc.algebraMap_ne_zero f.denom_ne_zero)
      (RatFunc.algebraMap_ne_zero g.denom_ne_zero), map_add, map_mul, map_mul, map_mul]
  rw [key, ordAt_div a hN (mul_ne_zero f.denom_ne_zero g.denom_ne_zero),
    Polynomial.rootMultiplicity_mul (mul_ne_zero f.denom_ne_zero g.denom_ne_zero)]
  simp only [ordAt] at hf hg
  set M : ℤ := n + (f.denom.rootMultiplicity a : ℤ) + (g.denom.rootMultiplicity a : ℤ) with hM
  rcases le_or_gt M 0 with hM0 | hM0
  · have : (0 : ℤ) ≤ (f.denom.rootMultiplicity a : ℤ) := Int.natCast_nonneg _
    have : (0 : ℤ) ≤ ((f.num * g.denom + f.denom * g.num).rootMultiplicity a : ℤ) :=
      Int.natCast_nonneg _
    omega
  · lift M to ℕ using le_of_lt hM0 with M' hM'
    have hd1 : ((X : k[X]) - C a) ^ M' ∣ f.num * g.denom := by
      refine pow_dvd_of_le_rootMultiplicity ?_
      rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (RatFunc.num_ne_zero hf0)
        g.denom_ne_zero)]
      omega
    have hd2 : ((X : k[X]) - C a) ^ M' ∣ f.denom * g.num := by
      refine pow_dvd_of_le_rootMultiplicity ?_
      rw [Polynomial.rootMultiplicity_mul (mul_ne_zero f.denom_ne_zero
        (RatFunc.num_ne_zero hg0))]
      omega
    have : M' ≤ (f.num * g.denom + f.denom * g.num).rootMultiplicity a :=
      (Polynomial.le_rootMultiplicity_iff hN).2 (dvd_add hd1 hd2)
    omega

/-- The ultrametric inequality at the place at infinity. -/
