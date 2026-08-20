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


lemma gmean_congr (hA : A.PosDef) (hB : B.PosSemidef) {T : Matrix n n ℂ} (hT : IsUnit T) :
    gmean (T * A * Tᴴ) (T * B * Tᴴ) = T * gmean A B * Tᴴ := by
  have hTH : IsUnit (Tᴴ) := hT.star
  have hTinv : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det T).1 hT)
  have hTinv' : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det T).1 hT)
  have hTHinv : Tᴴ * (Tᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hTH)
  have hTHinv' : (Tᴴ)⁻¹ * Tᴴ = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hTH)
  have hApos : (T * A * Tᴴ).PosDef := by
    rw [show (Tᴴ : Matrix n n ℂ) = star T from rfl]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hT).2 hA
  refine gmean.eq_of hApos ?_ ?_
  · have := (gmean.posSemidef hA hB).conjTranspose_mul_mul_same (Tᴴ)
    simpa [Matrix.mul_assoc] using this
  · have hinv : (T * A * Tᴴ)⁻¹ = (Tᴴ)⁻¹ * A⁻¹ * T⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
    rw [hinv]
    calc T * gmean A B * Tᴴ * ((Tᴴ)⁻¹ * A⁻¹ * T⁻¹) * (T * gmean A B * Tᴴ)
        = T * gmean A B * ((Tᴴ * (Tᴴ)⁻¹) * A⁻¹ * (T⁻¹ * T)) * gmean A B * Tᴴ := by noncomm_ring
      _ = T * (gmean A B * A⁻¹ * gmean A B) * Tᴴ := by
          rw [hTHinv, hTinv']; noncomm_ring
      _ = T * B * Tᴴ := by rw [gmean.mul_inv_mul hA hB]

/-- The geometric mean of two diagonal matrices. -/
