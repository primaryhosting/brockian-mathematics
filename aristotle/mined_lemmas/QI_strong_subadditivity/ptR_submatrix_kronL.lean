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


lemma ptR_submatrix_kronL (N : Matrix (β × γ) (β × γ) ℂ) :
    ptR ((((1 : Matrix α α ℂ) ⊗ₖ N)).submatrix (assocEquiv α β γ).symm
        (assocEquiv α β γ).symm)
      = (1 : Matrix α α ℂ) ⊗ₖ (ptR N) := by
  ext p q
  simp only [ptR_apply, Matrix.submatrix_apply, assocEquiv_symm_apply,
    Matrix.kroneckerMap_apply]
  show ∑ x : γ, (1 : Matrix α α ℂ) p.1 q.1 * N (p.2, x) (q.2, x)
      = (1 : Matrix α α ℂ) p.1 q.1 * ∑ c, N (p.2, c) (q.2, c)
  rw [← Finset.mul_sum]

/-! ### The main theorem -/

/-- **Strong subadditivity of the von Neumann entropy** (Lieb–Ruskai).

For a positive definite matrix `ρ` on `α ⊗ β ⊗ γ`, with marginals `ρ_AB = Tr_γ ρ`,
`ρ_BC = Tr_α ρ` and `ρ_B = Tr_γ ρ_BC`, the von Neumann entropy `S(A) = -Tr (A log A)`
satisfies `S(ρ) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.  (No normalisation of `ρ` is needed.) -/
