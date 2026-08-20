/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is a
-- plain comment and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Set Topology
open scoped ComplexInnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section Aux


theorem hasGenerator_symmetric (hU : IsUnitaryGroup U) {x₁ y₁ x₂ y₂ : H}
    (h₁ : HasGenerator U x₁ y₁) (h₂ : HasGenerator U x₂ y₂) : ⟪y₁, x₂⟫ = ⟪x₁, y₂⟫ := by
  have hA : Tendsto (fun t : ℝ => ⟪t⁻¹ • (U t x₁ - x₁), x₂⟫) (𝓝[≠] (0:ℝ))
      (𝓝 ⟪Complex.I • y₁, x₂⟫) := h₁.inner tendsto_const_nhds
  have hB : Tendsto (fun t : ℝ => ⟪x₁, t⁻¹ • (U t x₂ - x₂)⟫) (𝓝[≠] (0:ℝ))
      (𝓝 ⟪x₁, Complex.I • y₂⟫) := tendsto_const_nhds.inner h₂
  have hB' := (hB.comp tendsto_neg_punctured).neg
  have heq : ∀ t : ℝ, ⟪t⁻¹ • (U t x₁ - x₁), x₂⟫
      = -((fun t : ℝ => ⟪x₁, t⁻¹ • (U t x₂ - x₂)⟫) ∘ (fun t : ℝ => -t)) t := by
    intro t
    simp only [Function.comp_apply, inner_rsmul_left, inner_rsmul_right, inner_sub_left,
      inner_sub_right, inv_neg, Complex.ofReal_neg, Complex.ofReal_inv]
    rw [inner_apply_left hU t x₁ x₂]
    ring
  have hlim : ⟪Complex.I • y₁, x₂⟫ = -⟪x₁, Complex.I • y₂⟫ :=
    tendsto_nhds_unique (hA.congr fun t => heq t) hB'
  rw [inner_smul_left, inner_smul_right] at hlim
  simp only [Complex.conj_I] at hlim
  exact mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) (a := -Complex.I)
    (b := ⟪y₁, x₂⟫) (c := ⟪x₁, y₂⟫) (by linear_combination hlim)

end Basic

section Resolvent

variable [CompleteSpace H] {U : ℝ → (H ≃ₗᵢ[ℂ] H)}

/-- Resolvent construction: for every `x` there is a `w` in the domain of the generator `A`
with `A w = i • (x - w)`, i.e. `(A + i) w = i • x`.  Here
`w = ∫_0^∞ e^{-t} U t x dt = (1 - i A)⁻¹ x`. -/
