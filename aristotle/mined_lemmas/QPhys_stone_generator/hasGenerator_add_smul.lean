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


theorem hasGenerator_add_smul {c : ℂ} {x₁ y₁ x₂ y₂ : H} (h₁ : HasGenerator U x₁ y₁)
    (h₂ : HasGenerator U x₂ y₂) : HasGenerator U (x₁ + c • x₂) (y₁ + c • y₂) := by
  have hsum := h₁.add (h₂.const_smul c)
  have heq : ∀ t : ℝ, t⁻¹ • (U t x₁ - x₁) + c • (t⁻¹ • (U t x₂ - x₂))
      = t⁻¹ • (U t (x₁ + c • x₂) - (x₁ + c • x₂)) := by
    intro t
    simp only [map_add, map_smul, smul_sub, smul_add]
    simp only [smul_comm c (t⁻¹ : ℝ)]
    abel
  have hval : Complex.I • y₁ + c • Complex.I • y₂ = Complex.I • (y₁ + c • y₂) := by
    rw [smul_add, smul_comm c Complex.I]
  rw [HasGenerator, ← hval]
  exact hsum.congr heq

/-- The generator is symmetric. -/
