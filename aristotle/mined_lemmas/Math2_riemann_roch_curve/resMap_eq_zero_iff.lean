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

lemma resMap_eq_zero_iff (p : P) (n : ℤ) {V : Type*} [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] F) (hf : ∀ v, ((-n : ℤ) : Zt) ≤ C.ord p (f v)) (v : V) :
    C.resMap p n f hf v = 0 ↔ (((1 - n : ℤ)) : Zt) ≤ C.ord p (f v) := by
  rw [resMap]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h
    have h1 : ((1 : ℤ) : Zt) ≤ C.ord p (C.unif p ^ n * f v) := h
    exact C.ord_shift_le p n 1 (f v) h1
  · intro h
    show ((1 : ℤ) : Zt) ≤ C.ord p (C.unif p ^ n * f v)
    have := C.ord_shift_ge p n (1 - n) (f v) h
    simpa using this

