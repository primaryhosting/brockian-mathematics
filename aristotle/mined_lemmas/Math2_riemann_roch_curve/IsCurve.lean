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

lemma IsCurve.chi_step (hC : C.IsCurve) (D : P →₀ ℤ) (p : P) (h : Module.Finite K (C.H1 D)) :
    (C.ell (D + Finsupp.single p 1) : ℤ) - C.iH (D + Finsupp.single p 1)
      = (C.ell D : ℤ) - C.iH D + C.deg p := by
  haveI := hC.residue_finite p
  have h1 := hC.finrank_H1_add D p h
  have h2 : finrank K (LinearMap.range (C.psi D (D + Finsupp.single p 1))) =
      finrank K (C.resField p ⧸ LinearMap.range (C.resL (D + Finsupp.single p 1) p)) :=
    LinearEquiv.finrank_eq (C.rangePsiEquiv D p)
  have h3 := hC.finrank_resField_quot (D + Finsupp.single p 1) p
  have h4 := hC.finrank_range_resL (D + Finsupp.single p 1) p
  rw [add_single_sub_single D p] at h4
  rw [h2] at h1
  omega

end PreCurve

end Math2

/-
The residue fields of the projective line.
-/
import RequestProject.P1.Curve

namespace Math2

namespace P1

open Polynomial RatFunc Module Submodule

universe u

variable {K : Type u} [Field K]

