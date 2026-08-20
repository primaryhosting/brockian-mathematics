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


theorem exists_hasGenerator_sub (hU : IsUnitaryGroup U) (x : H) :
    ∃ w : H, HasGenerator U w (Complex.I • (w - x)) := by
  have hV : IsUnitaryGroup (fun t => U (-t)) := by
    refine ⟨by simpa using hU.zero, ?_, fun x => (hU.cont x).comp continuous_neg⟩
    intro s t x
    show U (-(s + t)) x = U (-s) (U (-t) x)
    rw [neg_add]
    exact hU.add _ _ _
  obtain ⟨w, hw⟩ := exists_hasGenerator_add hV x
  refine ⟨w, ?_⟩
  have h := (hw.comp tendsto_neg_punctured).neg
  have heq : ∀ t : ℝ, -((fun t : ℝ => t⁻¹ • ((fun t => U (-t)) t w - w)) ∘ (fun t : ℝ => -t)) t
      = t⁻¹ • (U t w - w) := by
    intro t
    simp [inv_neg]
  have hval : -(Complex.I • (Complex.I • (x - w))) = Complex.I • (Complex.I • (w - x)) := by
    rw [smul_smul, smul_smul, Complex.I_mul_I]
    module
  rw [HasGenerator, ← hval]
  exact h.congr heq

end Resolvent

section Main

variable [CompleteSpace H] {U : ℝ → (H ≃ₗᵢ[ℂ] H)}

/-- `A + i` is surjective. -/
