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


lemma eq_of {X : Matrix n n ℂ} (hX : X.PosSemidef) (h : X * A⁻¹ * X = B) : gmean A B = X := by
  set S := CFC.sqrt A with hS
  have hXY : (S⁻¹ * X * S⁻¹).PosSemidef := by
    have := hX.conjTranspose_mul_mul_same (S⁻¹)
    rwa [(inv_sqrt_herm hA).eq] at this
  have key : (S⁻¹ * X * S⁻¹) * (S⁻¹ * X * S⁻¹) = S⁻¹ * B * S⁻¹ := by
    rw [← h, inv_eq hA]; noncomm_ring
  have hsq : CFC.sqrt (S⁻¹ * B * S⁻¹) = S⁻¹ * X * S⁻¹ := by
    rw [CFC.sqrt_eq_iff _ _ ?_ hXY.nonneg]
    · exact key
    · rw [← key]
      have : ((S⁻¹ * X * S⁻¹) * (S⁻¹ * X * S⁻¹)).PosSemidef := by
        have h1 := Matrix.posSemidef_conjTranspose_mul_self (S⁻¹ * X * S⁻¹)
        rwa [hXY.1.eq] at h1
      exact this.nonneg
  show S * CFC.sqrt (S⁻¹ * B * S⁻¹) * S = X
  rw [hsq]
  exact conj_sqrt_conj_inv hA X

end gmean

/-- Maximality of the geometric mean. -/
