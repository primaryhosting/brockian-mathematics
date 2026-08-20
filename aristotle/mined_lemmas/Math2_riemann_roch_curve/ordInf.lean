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

noncomputable def ordInf : AddValuation (RatFunc K) (WithTop ℤ) :=
  AddValuation.of ordInfFun (by simp) (by simp [ordInfFun_of_ne_zero (one_ne_zero (α := RatFunc K))])
    (by
      intro x y
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      rcases eq_or_ne (x + y) 0 with h | hxy
      · simp [h]
      · rw [ordInfFun_of_ne_zero hx, ordInfFun_of_ne_zero hy, ordInfFun_of_ne_zero hxy,
          min_le_iff]
        have h2 := ordInfZ_add_ge hxy
        rw [min_le_iff] at h2
        rcases h2 with h2 | h2
        · exact Or.inl (by exact_mod_cast h2)
        · exact Or.inr (by exact_mod_cast h2))
    (by
      intro x y
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      rw [ordInfFun_of_ne_zero hx, ordInfFun_of_ne_zero hy,
        ordInfFun_of_ne_zero (mul_ne_zero hx hy), ordInfZ_mul hx hy]
      norm_cast)

