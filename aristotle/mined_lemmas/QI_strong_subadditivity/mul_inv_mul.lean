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


lemma mul_inv_mul : gmean A B * A⁻¹ * gmean A B = B := by
  set S := CFC.sqrt A with hS
  set C := CFC.sqrt (S⁻¹ * B * S⁻¹) with hC
  have hCC : C * C = S⁻¹ * B * S⁻¹ :=
    CFC.sqrt_mul_sqrt_self _ (inner_posSemidef hA hB).nonneg
  show (S * C * S) * A⁻¹ * (S * C * S) = B
  rw [inv_eq hA]
  calc (S * C * S) * (S⁻¹ * S⁻¹) * (S * C * S)
      = S * C * ((S * S⁻¹) * (S⁻¹ * S)) * C * S := by noncomm_ring
    _ = S * (C * C) * S := by
        rw [sqrt_mul_inv hA, inv_mul_sqrt hA]; noncomm_ring
    _ = S * (S⁻¹ * B * S⁻¹) * S := by rw [hCC]
    _ = B := conj_sqrt_conj_inv hA B

omit hB in
/-- Uniqueness: the geometric mean is the unique positive semidefinite solution of
`X * A⁻¹ * X = B`. -/
