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

def FSub : Submodule K C.Adele := LinearMap.range C.diagLin

/-- The first cohomology `H¹(D) = A / (A(D) + F)`. -/
abbrev H1 (D : P →₀ ℤ) : Type _ := C.Adele ⧸ (C.AD D ⊔ C.FSub)

/-- The additional axioms making a `PreCurve` into a (smooth projective) curve: the residue
field at each place is a finite extension of `K` whose degree is the degree of the place,
and the curve is proper, i.e. some first cohomology group is finite dimensional. -/
structure IsCurve : Prop where
  /-- Each residue field is a finite extension of `K`. -/
  residue_finite : ∀ p : P, Module.Finite K (C.resField p)
  /-- The degree of a place is the degree of its residue field. -/
  residue_finrank : ∀ p : P, Module.finrank K (C.resField p) = C.deg p
  /-- Properness: some cohomology group is finite dimensional. -/
  properness : ∃ D : P →₀ ℤ, Module.Finite K (C.H1 D)

end PreCurve

end Math2

/-
The key step: comparing `H¹(D)` and `H¹(D + p)`.
-/
import RequestProject.Math2.Adeles

namespace Math2

open Module Submodule

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable (C : PreCurve K F P)

/-- The map `A(E) → H¹(D)`. -/
