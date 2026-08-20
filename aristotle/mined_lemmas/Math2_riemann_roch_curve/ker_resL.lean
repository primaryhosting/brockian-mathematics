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

lemma ker_resL (E : P →₀ ℤ) (p : P) :
    LinearMap.ker (C.resL E p) = (C.LSpace (E - Finsupp.single p 1)).comap
      (C.LSpace E).subtype := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
  rw [resL, C.resMap_eq_zero_iff]
  constructor
  · intro h q
    rcases eq_or_ne q p with rfl | hq
    · simpa using h
    · have := x.2 q
      simpa [Finsupp.single_apply, hq] using this
  · intro h
    have := h p
    simpa using this

/-- `ell D` is the dimension of the Riemann-Roch space `L(D)`. -/
