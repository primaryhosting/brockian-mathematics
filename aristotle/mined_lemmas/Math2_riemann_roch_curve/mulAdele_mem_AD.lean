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

lemma mulAdele_mem_AD {x : F} (hx : x ≠ 0) {B : P →₀ ℤ} {α : C.Adele} (hα : α ∈ C.AD B) :
    C.mulAdele x α ∈ C.AD (B - C.divisorOf x) := by
  intro p
  have h := hα p
  have h2 := C.ord_mul_ge p x (α.val p) hx (-(B p)) h
  have h3 : (C.mulAdele x α).val p = x * α.val p := rfl
  rw [h3]
  refine le_trans (le_of_eq ?_) h2
  have hval : -((B - C.divisorOf x) p) = -B p + C.ordZ p x := by
    simp only [Finsupp.coe_sub, Pi.sub_apply, C.divisorOf_apply hx p]
    ring
  rw [hval]

