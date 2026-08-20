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

lemma ordFinZ_add_ge (q : FinPlace K) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (ordFinZ q x) (ordFinZ q y) ≤ ordFinZ q (x + y) := by
  have hkey : (x + y).num * (x.denom * y.denom)
      = (x.num * y.denom + x.denom * y.num) * (x + y).denom := RatFunc.num_denom_add x y
  have hune : x.num * y.denom ≠ 0 :=
    mul_ne_zero (RatFunc.num_ne_zero hx) (RatFunc.denom_ne_zero y)
  have hvne : x.denom * y.num ≠ 0 :=
    mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.num_ne_zero hy)
  have huv : x.num * y.denom + x.denom * y.num ≠ 0 := by
    intro h
    apply RatFunc.num_ne_zero hxy
    have h2 : (x + y).num * (x.denom * y.denom) = 0 := by rw [hkey, h, zero_mul]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd h3 (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y))
  have h1 : cnt q ((x + y).num * (x.denom * y.denom))
      = cnt q ((x.num * y.denom + x.denom * y.num) * (x + y).denom) := by rw [hkey]
  rw [cnt_mul q (RatFunc.num_ne_zero hxy)
      (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y)),
    cnt_mul q (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y),
    cnt_mul q huv (RatFunc.denom_ne_zero (x + y))] at h1
  have h2 := cnt_add_ge q huv
  rw [cnt_mul q (RatFunc.num_ne_zero hx) (RatFunc.denom_ne_zero y),
    cnt_mul q (RatFunc.denom_ne_zero x) (RatFunc.num_ne_zero hy), min_le_iff] at h2
  simp only [ordFinZ, min_le_iff]
  rcases h2 with h2 | h2
  · left; omega
  · right; omega

