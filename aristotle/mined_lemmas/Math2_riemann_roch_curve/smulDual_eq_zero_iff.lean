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

lemma smulDual_eq_zero_iff {x : F} (hx : x ≠ 0) (ω : Module.Dual K C.Adele) :
    C.smulDual x ω = 0 ↔ ω = 0 := by
  constructor
  · intro h
    have : C.smulDual x⁻¹ (C.smulDual x ω) = 0 := by rw [h]; ext α; simp
    rw [← C.smulDual_mul, inv_mul_cancel₀ hx, C.smulDual_one] at this
    exact this
  · intro h; rw [h]; ext α; simp

end PreCurve

end Math2

/-
Finiteness of all cohomology groups, the genus, and the Riemann part of Riemann-Roch.
-/
import RequestProject.Math2.Chi

namespace Math2

open Module Submodule

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable (C : PreCurve K F P)

/-- The Euler characteristic `ell(D) - i(D)`. -/
