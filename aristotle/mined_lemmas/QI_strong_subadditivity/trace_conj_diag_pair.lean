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


lemma trace_conj_diag_pair (U V : Matrix n n ℂ) (d e : n → ℝ) :
    ((U * diagonal (fun i => (d i : ℂ)) * star U) *
        (V * diagonal (fun j => (e j : ℂ)) * star V)).trace
      = ∑ i, ∑ j, ((d i * e j * Complex.normSq ((star U * V) i j) : ℝ) : ℂ) := by
  set Df : Matrix n n ℂ := diagonal (fun i => (d i : ℂ))
  set Dg : Matrix n n ℂ := diagonal (fun j => (e j : ℂ))
  have hWH : (star U * V : Matrix n n ℂ)ᴴ = star V * U := by
    simp [star_eq_conjTranspose, Matrix.conjTranspose_mul]
  have e1 : (U * Df * star U * (V * Dg * star V)) = (U * Df * star U * V * Dg) * star V := by
    noncomm_ring
  have e2 : ((U * Df * star U * (V * Dg * star V))).trace
      = (Df * (star U * V) * Dg * (star V * U)).trace := by
    rw [e1, Matrix.trace_mul_comm, Matrix.trace_mul_comm (Df * (star U * V) * Dg)]
    congr 1
    noncomm_ring
  rw [e2, ← hWH, trace_diagonal_conj]

end trace

variable {A B : Matrix n n ℂ}

/-- The overlap matrix between the eigenbases of two hermitian matrices; it is doubly
stochastic. -/
