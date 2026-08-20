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

noncomputable def rangePsiEquiv (D : P →₀ ℤ) (p : P) :
    ↥(LinearMap.range (C.psi D (D + Finsupp.single p 1))) ≃ₗ[K]
      (C.resField p ⧸ LinearMap.range (C.resL (D + Finsupp.single p 1) p)) :=
  let e1 : ↥(LinearMap.range (C.psi D (D + Finsupp.single p 1))) ≃ₗ[K]
      (↥(C.AD (D + Finsupp.single p 1)) ⧸ LinearMap.ker (C.psi D (D + Finsupp.single p 1))) :=
    (LinearMap.quotKerEquivRange (C.psi D (D + Finsupp.single p 1))).symm
  let e2 : (↥(C.AD (D + Finsupp.single p 1)) ⧸ LinearMap.ker (C.psi D (D + Finsupp.single p 1)))
      ≃ₗ[K] (↥(C.AD (D + Finsupp.single p 1)) ⧸
        LinearMap.ker (C.resQuotMap (D + Finsupp.single p 1) p)) :=
    Submodule.quotEquivOfEq _ _ (C.ker_resQuotMap_eq_ker_psi D p).symm
  let e3 : (↥(C.AD (D + Finsupp.single p 1)) ⧸ LinearMap.ker (C.resQuotMap (D + Finsupp.single p 1) p))
      ≃ₗ[K] (C.resField p ⧸ LinearMap.range (C.resL (D + Finsupp.single p 1) p)) :=
    LinearMap.quotKerEquivOfSurjective _ (C.resQuotMap_surjective (D + Finsupp.single p 1) p)
  e1.trans (e2.trans e3)

