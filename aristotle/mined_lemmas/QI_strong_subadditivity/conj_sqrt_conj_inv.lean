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


lemma conj_sqrt_conj_inv (X : Matrix n n ℂ) :
    CFC.sqrt A * ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt A)⁻¹) * CFC.sqrt A = X := by
  calc CFC.sqrt A * ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt A)⁻¹) * CFC.sqrt A
      = (CFC.sqrt A * (CFC.sqrt A)⁻¹) * X * ((CFC.sqrt A)⁻¹ * CFC.sqrt A) := by noncomm_ring
    _ = X := by rw [sqrt_mul_inv hA, inv_mul_sqrt hA, one_mul, mul_one]

include hB

