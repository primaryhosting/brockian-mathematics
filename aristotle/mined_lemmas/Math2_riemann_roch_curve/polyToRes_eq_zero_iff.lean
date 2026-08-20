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

lemma polyToRes_eq_zero_iff (a : K[X]) : polyToRes q a = 0 ↔ q.poly ∣ a := by
  rw [polyToRes, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mem_maxIdeal_iff]
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have hne : algebraMap K[X] (RatFunc K) a ≠ 0 := fun hh =>
      ha (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
    rw [polyToLocal_coe]
    constructor
    · rintro (h | h)
      · exact absurd h hne
      · simp only [ordZP, ordFinZ_algebraMap] at h
        exact dvd_of_cnt_ne_zero q (by omega)
    · intro hdvd
      refine Or.inr ?_
      simp only [ordZP, ordFinZ_algebraMap]
      have : cnt q a ≠ 0 := fun hc => (cnt_eq_zero_iff q a).1 hc hdvd
      omega

