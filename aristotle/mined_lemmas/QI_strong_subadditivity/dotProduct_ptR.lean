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


private lemma dotProduct_ptR (M : Matrix (β × γ) (β × γ) ℂ) (x : β → ℂ) :
    star x ⬝ᵥ (ptR M) *ᵥ x = ∑ c, star (sliceVec x c) ⬝ᵥ M *ᵥ (sliceVec x c) := by
  classical
  have hL : star x ⬝ᵥ (ptR M) *ᵥ x = ∑ b : β, ∑ b' : β, ∑ c : γ,
      (starRingEnd ℂ) (x b) * (M (b, c) (b', c) * x b') := by
    simp [dotProduct, Matrix.mulVec, ptR, Finset.mul_sum, Finset.sum_mul]
  rw [hL, Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) => dotProduct_sliceVec M x c)]
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => Finset.sum_comm)]
  exact Finset.sum_comm

