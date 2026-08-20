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


lemma relEnt_kronL_self {δ : Type*} [Fintype δ] [DecidableEq δ]
    {R : Matrix (α × δ) (α × δ) ℂ} (hR : (ptL R).PosDef) :
    relEnt R ((1 : Matrix α α ℂ) ⊗ₖ (ptL R)) = -vnEnt R + vnEnt (ptL R) := by
  have h : vnEnt (ptL R) = -((ptL R * CFC.log (ptL R)).trace).re := by rw [vnEnt]; simp
  rw [relEnt_kronL_eq hR, h]
  ring

/-! ### The three marginals -/

/-- The reindexing `α × (β × γ) ≃ (α × β) × γ`. -/
