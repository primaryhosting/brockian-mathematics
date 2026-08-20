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


lemma scalar_klein {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x - y ≤ x * (Real.log x - Real.log y) := by
  rcases eq_or_lt_of_le hx with h | hx'
  · simp [← h]
    linarith
  · have h1 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx')] at h1
    have h2 : x * (Real.log y - Real.log x) ≤ x * (y / x - 1) :=
      mul_le_mul_of_nonneg_left h1 hx
    have h3 : x * (y / x - 1) = y - x := by field_simp
    rw [h3] at h2
    nlinarith [h2]

/-- **Klein's inequality**. -/
