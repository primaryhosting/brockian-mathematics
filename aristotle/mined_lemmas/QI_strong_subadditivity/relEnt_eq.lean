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


lemma relEnt_eq (hA : A.IsHermitian) (hB : B.IsHermitian) :
    relEnt A B = ∑ i, ∑ j, ovl hA hB i j *
      (hA.eigenvalues i * (Real.log (hA.eigenvalues i) - Real.log (hB.eigenvalues j))) := by
  have hsplit : A * (CFC.log A - CFC.log B) = A * CFC.log A - A * CFC.log B := by
    rw [mul_sub]
  rw [relEnt, hsplit, Matrix.trace_sub, trace_mul_log_self hA, trace_mul_log hA hB]
  rw [← Complex.ofReal_sum]
  have h2 : (∑ i, ∑ j, ((hA.eigenvalues i * Real.log (hB.eigenvalues j) * ovl hA hB i j : ℝ) : ℂ))
      = ((∑ i, ∑ j, hA.eigenvalues i * Real.log (hB.eigenvalues j) * ovl hA hB i j : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h2, ← Complex.ofReal_sub, Complex.ofReal_re]
  have h3 : ∑ i, hA.eigenvalues i * Real.log (hA.eigenvalues i)
      = ∑ i, ∑ j, ovl hA hB i j * (hA.eigenvalues i * Real.log (hA.eigenvalues i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, ovl_sum_right hA hB i, one_mul]
  rw [h3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The scalar inequality behind Klein's inequality. -/
