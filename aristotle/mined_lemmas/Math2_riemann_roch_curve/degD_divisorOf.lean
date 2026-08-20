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

lemma degD_divisorOf {x : F} (hx : x ≠ 0) : C.degD (C.divisorOf x) = 0 := by
  classical
  set S := (C.ord_support x hx).choose with hS
  have hsupp : ∀ p ∉ S, C.ord p x = (0 : Zt) := (C.ord_support x hx).choose_spec
  have hsub : (C.divisorOf x).support ⊆ S := by
    intro p hp
    rw [divisorOf, dif_neg hx] at hp
    exact Finsupp.support_onFinset_subset hp
  rw [C.degD_eq_sum hsub]
  have h0 := C.degree_principal x hx S hsupp
  rw [← h0]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [C.divisorOf_apply hx p]
  simp only [ordZ]
  ring

/-! ### Weil differentials -/

/-- The space of Weil differentials with pole divisor bounded by `A`:
linear functionals on the adeles vanishing on `A(A) + F`. -/
