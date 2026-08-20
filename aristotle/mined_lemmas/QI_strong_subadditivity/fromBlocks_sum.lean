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


lemma fromBlocks_sum {ι : Type*} (s : Finset ι) (f g h k : ι → Matrix n n ℂ) :
    Matrix.fromBlocks (∑ i ∈ s, f i) (∑ i ∈ s, g i) (∑ i ∈ s, h i) (∑ i ∈ s, k i)
      = ∑ i ∈ s, Matrix.fromBlocks (f i) (g i) (h i) (k i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Matrix.fromBlocks_zero]
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha, ← ih, Matrix.fromBlocks_add]

end Blocks

/-- **Joint concavity of the operator geometric mean** (Ando's theorem), in the form of a
finite weighted sum. -/
