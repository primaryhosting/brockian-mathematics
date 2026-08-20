/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring; the required header is
-- reproduced verbatim as the module docstring immediately below the import.)

import RequestProject.Math2.Canonical

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

For a smooth projective curve, described here through its function field `F / K` with its
family of places `P` (see `Math2.PreCurve` and `Math2.PreCurve.IsCurve`), there exists a
*canonical divisor* `W` such that for every divisor `D`

  `ℓ(D) - ℓ(W - D) = deg D + 1 - g`,

where `ℓ(D) = dim_K L(D)` is the dimension of the Riemann-Roch space of `D`, `deg D` is the
degree of `D` and `g` is the genus of the curve.  The canonical divisor moreover satisfies
`ℓ(W) = g` and `deg W = 2g - 2`.
-/

namespace Math2

open PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]

/-- **Riemann-Roch for a smooth projective curve.**

There is a canonical divisor `W` (of degree `2g - 2` and with `ℓ(W) = g`) such that for every
divisor `D` on the curve,
`ℓ(D) - ℓ(W - D) = deg D + 1 - g`. -/

lemma ordFinZ_div (q : FinPlace K) {a b : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordFinZ q (algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b)
      = (cnt q a : ℤ) - cnt q b := by
  have hane : algebraMap K[X] (RatFunc K) a ≠ 0 := fun h =>
    ha (RatFunc.algebraMap_injective K (h.trans (map_zero _).symm))
  have hbne : algebraMap K[X] (RatFunc K) b ≠ 0 := fun h =>
    hb (RatFunc.algebraMap_injective K (h.trans (map_zero _).symm))
  rw [div_eq_mul_inv, ordFinZ_mul q hane (inv_ne_zero hbne), ordFinZ_inv q hbne,
    ordFinZ_algebraMap, ordFinZ_algebraMap]
  ring

open Classical in
/-- The additive valuation at a finite place. -/
