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

lemma smulDual_mem_OmegaSub_of_mem_LSpace {A D : P →₀ ℤ} {ω : Module.Dual K C.Adele}
    (hω : ω ∈ C.OmegaSub A) {x : F} (hx : x ∈ C.LSpace (A - D)) :
    C.smulDual x ω ∈ C.OmegaSub D := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [C.smulDual_zero_left]
    exact Submodule.zero_mem _
  · have hmem := mem_OmegaSub_smulDual hx0 hω
    refine C.OmegaSub_antitone ?_ hmem
    intro p
    have h := hx p
    rw [C.ord_eq_ordZ hx0] at h
    have h2 : -((A - D) p) ≤ C.ordZ p x := by exact_mod_cast h
    simp only [Finsupp.coe_sub, Pi.sub_apply] at h2
    simp only [Finsupp.coe_add, Pi.add_apply, C.divisorOf_apply hx0 p]
    omega

/-! ### Existence of a nonzero Weil differential -/

