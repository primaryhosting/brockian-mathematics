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


lemma liftR_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ) (B : ι → Matrix n n ℂ) :
    liftR (∑ i ∈ s, w i • B i) = ∑ i ∈ s, w i • liftR (B i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [liftR]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, liftR, liftR,
        Matrix.transpose_add, Matrix.kronecker_add, Matrix.transpose_smul,
        Matrix.kronecker_smul]
      rfl

/-- `Qd m A B = Tr (A ^ (1 - 2⁻ᵐ) * B ^ (2⁻ᵐ))`, defined through the geometric mean of the
lifted multiplication operators. -/
