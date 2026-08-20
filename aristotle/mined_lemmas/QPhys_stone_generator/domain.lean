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


def domain (U : ℝ → (H ≃ₗᵢ[ℂ] H)) : Submodule ℂ H where
  carrier := {x : H | ∃ y, HasGenerator U x y}
  add_mem' := by
    rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
    refine ⟨ya + (1 : ℂ) • yb, ?_⟩
    have := hasGenerator_add_smul (c := (1:ℂ)) ha hb
    rwa [one_smul] at this
  zero_mem' := ⟨0, hasGenerator_zero⟩
  smul_mem' := by
    rintro c a ⟨ya, ha⟩
    refine ⟨(0 : H) + c • ya, ?_⟩
    have := hasGenerator_add_smul (c := c) (hasGenerator_zero (U := U)) ha
    rwa [zero_add] at this

omit [CompleteSpace H] in
