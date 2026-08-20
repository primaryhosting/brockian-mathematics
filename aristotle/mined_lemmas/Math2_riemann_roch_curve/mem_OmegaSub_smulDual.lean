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

lemma mem_OmegaSub_smulDual {x : F} (hx : x ≠ 0) {A : P →₀ ℤ} {ω : Module.Dual K C.Adele}
    (hω : ω ∈ C.OmegaSub A) : C.smulDual x ω ∈ C.OmegaSub (A + C.divisorOf x) := by
  rw [mem_OmegaSub_iff]
  intro α hα
  rw [smulDual_apply]
  rw [mem_OmegaSub_iff] at hω
  refine hω _ ?_
  have hsub : C.AD (A + C.divisorOf x) ⊔ C.FSub ≤
      Submodule.comap (C.mulAdele x) (C.AD A ⊔ C.FSub) := by
    refine sup_le ?_ ?_
    · intro β hβ
      have h := mulAdele_mem_AD hx hβ
      have heq : A + C.divisorOf x - C.divisorOf x = A := by abel
      rw [heq] at h
      exact Submodule.mem_sup_left h
    · rintro β ⟨y, rfl⟩
      refine Submodule.mem_sup_right ?_
      rw [C.mulAdele_diagLin]
      exact ⟨x * y, rfl⟩
  exact hsub hα

/-- Multiplication of a fixed differential by functions, as a linear map. -/
