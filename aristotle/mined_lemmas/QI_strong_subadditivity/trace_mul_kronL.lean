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


lemma trace_mul_kronL (M : Matrix (β × γ) (β × γ) ℂ) (Z : Matrix γ γ ℂ) :
    (M * ((1 : Matrix β β ℂ) ⊗ₖ Z)).trace = ((ptL M) * Z).trace := by
  classical
  have hL : (M * ((1 : Matrix β β ℂ) ⊗ₖ Z)).trace
      = ∑ d : γ, ∑ d' : γ, ∑ a : β, M (a, d) (a, d') * Z d' d := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      one_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    have key : ∀ a : β, (∑ a' : β, ∑ d' : γ, (if a' = a then M (a, d) (a', d') * Z d' d else 0))
        = ∑ d' : γ, M (a, d) (a, d') * Z d' d := by
      intro a
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d' _ => ?_
      simp
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => key a)]
    exact Finset.sum_comm
  have hR : ((ptL M) * Z).trace = ∑ d : γ, ∑ d' : γ, ∑ a : β, M (a, d) (a, d') * Z d' d := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, ptL, Matrix.of_apply,
      Finset.sum_mul]
  rw [hL, hR]

/-! ### Stage 1 of the twirl: averaging over sign flips -/

/-- The `±1` valued character attached to a subset of `γ`. -/
