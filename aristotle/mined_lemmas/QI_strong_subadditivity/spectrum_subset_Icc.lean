import RequestProject.SSA.PartialTrace

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to follow the `import` line: Lean requires `import` commands to
come first in a file.)

The von Neumann entropy `S(A) = -Tr (A log A)` of a positive definite matrix on a threefold
tensor product `α ⊗ β ⊗ γ` satisfies the Lieb–Ruskai inequality

`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.

The proof goes through Lindblad's joint convexity of the Umegaki relative entropy
(itself deduced from Ando's joint concavity of the operator geometric mean) and the
resulting monotonicity of the relative entropy under partial traces.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-! ### Relative entropy against `1 ⊗ Y` -/


lemma spectrum_subset_Icc [Nonempty n] {A : Matrix n n ℂ} {r : ℝ} (h : ‖A‖ ≤ r) :
    spectrum ℝ A ⊆ Set.Icc (-r) r := by
  intro x hx
  have h1 := spectrum.norm_le_norm_of_mem (𝕜 := ℝ) hx
  rw [Real.norm_eq_abs] at h1
  exact ⟨(abs_le.1 (h1.trans h)).1, (abs_le.1 (h1.trans h)).2⟩

/-- **Continuity of the von Neumann entropy** on hermitian matrices. -/
