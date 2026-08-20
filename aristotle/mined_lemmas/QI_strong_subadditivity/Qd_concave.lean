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


theorem Qd_concave {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (A B : ι → Matrix n n ℂ) (hA : ∀ i ∈ s, (A i).PosDef) (hB : ∀ i ∈ s, (B i).PosSemidef)
    (hAsum : (∑ i ∈ s, w i • A i).PosDef) (m : ℕ) :
    ∑ i ∈ s, w i * Qd m (A i) (B i) ≤ Qd m (∑ i ∈ s, w i • A i) (∑ i ∈ s, w i • B i) := by
  have hlift : (∑ i ∈ s, w i • liftL (A i)).PosDef := by
    rw [← liftL_sum]
    exact liftL_posDef hAsum
  have h := gpow_concave s w hw (fun i => liftL (A i)) (fun i => liftR (B i))
    (fun i hi => liftL_posDef (hA i hi)) (fun i hi => liftR_posSemidef (hB i hi)) hlift m
  have hmono := qform_mono h
  rw [qform_sum] at hmono
  simp only [qform_smul] at hmono
  rw [Complex.re_sum] at hmono
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hmono
  rw [← liftL_sum, ← liftR_sum] at hmono
  exact hmono

/-- **Spectral evaluation** of `Qd`. -/
