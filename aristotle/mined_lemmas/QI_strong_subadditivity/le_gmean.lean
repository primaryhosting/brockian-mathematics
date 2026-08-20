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


lemma le_gmean (hA : A.PosDef) {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (h : X * A⁻¹ * X ≤ B) : X ≤ gmean A B := by
  set S := CFC.sqrt A with hS
  have hSherm : S.IsHermitian := sqrt_hermitian A
  have hSi : (S⁻¹).IsHermitian := gmean.inv_sqrt_herm hA
  set Y := S⁻¹ * X * S⁻¹ with hY
  have hYherm : Y.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hY]
    simp [Matrix.conjTranspose_mul, hX.eq, hSi.eq, Matrix.mul_assoc]
  have hYY : Y * Y = S⁻¹ * (X * A⁻¹ * X) * S⁻¹ := by
    rw [hY, gmean.inv_eq hA]; noncomm_ring
  have hle : Y * Y ≤ S⁻¹ * B * S⁻¹ := by
    rw [hYY]; exact conj_le_conj h hSi
  have habs : CFC.abs Y = CFC.sqrt (Y * Y) := by
    rw [CFC.abs, star_eq_conjTranspose, hYherm.eq]
  have h1 : Y ≤ CFC.abs Y := by
    rw [← sub_nonneg, CFC.abs_sub_self Y hYherm]
    exact nsmul_nonneg (CFC.negPart_nonneg Y) 2
  have h2 : CFC.sqrt (Y * Y) ≤ CFC.sqrt (S⁻¹ * B * S⁻¹) := CFC.monotone_sqrt hle
  have hYle : Y ≤ CFC.sqrt (S⁻¹ * B * S⁻¹) := le_trans h1 (habs ▸ h2)
  have hcon := conj_le_conj hYle hSherm
  rw [hY, gmean.conj_sqrt_conj_inv hA X] at hcon
  exact hcon

/-- Monotonicity of the geometric mean in its second argument. -/
