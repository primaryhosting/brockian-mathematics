/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/

theorem huckel_C14_hasEigenvalue_iff (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' C14adj : Module.End ℂ (ZMod 14 → ℂ)) μ ↔
      ∃ k : ℕ, k < 14 ∧ μ = ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ) := by
  rw [← huckel_C14]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    refine ⟨v, hv.2, ?_⟩
    have := Module.End.mem_eigenspace_iff.1 hv.1
    simpa [Matrix.toLin'_apply] using this
  · rintro ⟨v, hv0, hv⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector
      (x := v) ⟨Module.End.mem_eigenspace_iff.2 ?_, hv0⟩
    simpa [Matrix.toLin'_apply] using hv

/-- The set of eigenvalues of the `C₁₄` adjacency matrix is exactly
`{2 cos (2 π k / 14) : k = 0, …, 13}`. -/
