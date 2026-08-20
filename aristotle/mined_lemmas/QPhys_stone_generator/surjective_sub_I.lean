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


theorem surjective_sub_I (hU : IsUnitaryGroup U) (v : H) :
    ∃ w y, HasGenerator U w y ∧ y - Complex.I • w = v := by
  obtain ⟨w, hw⟩ := exists_hasGenerator_sub hU (Complex.I • v)
  refine ⟨w, _, hw, ?_⟩
  rw [smul_sub, smul_smul]
  simp [Complex.I_mul_I]

/-- The domain of the generator, as a linear subspace. -/
