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


theorem relEnt_kronR {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    relEnt (A ⊗ₖ (1 : Matrix m m ℂ)) (B ⊗ₖ (1 : Matrix m m ℂ))
      = (Fintype.card m : ℝ) * relEnt A B := by
  rw [relEnt, relEnt, log_kronR (m := m) hA, log_kronR (m := m) hB]
  have hsub : CFC.log A ⊗ₖ (1 : Matrix m m ℂ) - CFC.log B ⊗ₖ (1 : Matrix m m ℂ)
      = (CFC.log A - CFC.log B) ⊗ₖ (1 : Matrix m m ℂ) := by
    ext p q
    simp [Matrix.kroneckerMap_apply, sub_mul]
  rw [hsub, ← Matrix.mul_kronecker_mul, one_mul, Matrix.trace_kronecker,
    Matrix.trace_one]
  simp [Complex.mul_re, mul_comm]

end QI

import RequestProject.SSA.Lift

/-!
# Joint convexity of the relative entropy

Letting `m → ∞` in the jointly concave functionals
`Qd m A B = Tr (A ^ (1 - 2⁻ᵐ) * B ^ (2⁻ᵐ))` gives the relative entropy, whence its joint
convexity (Lindblad).
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix Filter Topology

set_option maxHeartbeats 1000000

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A B : Matrix n n ℂ}

/-- The scalar limit underlying the derivative formula for the relative entropy. -/
