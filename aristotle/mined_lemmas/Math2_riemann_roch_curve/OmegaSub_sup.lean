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

lemma OmegaSub_sup {A B : P →₀ ℤ} {ω : Module.Dual K C.Adele}
    (hA : ω ∈ C.OmegaSub A) (hB : ω ∈ C.OmegaSub B) : ω ∈ C.OmegaSub (A ⊔ B) := by
  rw [mem_OmegaSub_iff] at hA hB ⊢
  intro α hα
  rcases Submodule.mem_sup.1 hα with ⟨a, ha, y, hy, rfl⟩
  rcases Submodule.mem_sup.1 (C.AD_sup_le A B ha) with ⟨b, hb, c, hc, rfl⟩
  rw [map_add, map_add, hA b (Submodule.mem_sup_left hb),
    hB c (Submodule.mem_sup_left hc), hA y (Submodule.mem_sup_right hy)]
  simp

