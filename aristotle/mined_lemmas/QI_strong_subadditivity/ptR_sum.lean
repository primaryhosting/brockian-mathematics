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


lemma ptR_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ) (M : ι → Matrix (β × γ) (β × γ) ℂ) :
    ptR (∑ i ∈ s, w i • M i) = ∑ i ∈ s, w i • ptR (M i) := by
  classical
  induction s using Finset.induction with
  | empty => ext b b'; simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ptR_add, ptR_smul, ih]

