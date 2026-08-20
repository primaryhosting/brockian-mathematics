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


lemma gpow_diagonal {a b : n → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (m : ℕ) :
    gpow m (Matrix.diagonal fun i => (a i : ℂ)) (Matrix.diagonal fun i => (b i : ℂ))
      = Matrix.diagonal fun i => ((dyseq m (a i) (b i) : ℝ) : ℂ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [gpow_succ, ih]
      rw [gmean_diagonal ha (fun i => (dyseq_pos m (ha i) (hb i)).le)]
      rfl

end QI

import RequestProject.SSA.Invariance
import RequestProject.SSA.Convexity

/-!
# Partial traces

The partial trace over the right tensor factor, its basic properties, and the twirling
identities that express `Tr_γ M ⊗ 1` as an average of unitary conjugates of `M`.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- The partial trace over the right tensor factor. -/
