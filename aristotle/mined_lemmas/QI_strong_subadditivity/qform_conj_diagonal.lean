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


lemma qform_conj_diagonal (W : Matrix (n × n) (n × n) ℂ) (d : n × n → ℝ) :
    qform (W * diagonal (fun p => (d p : ℂ)) * Wᴴ)
      = ((∑ p : n × n, d p * Complex.normSq (∑ k, W (k, k) p) : ℝ) : ℂ) := by
  have step : ∀ i j : n, (W * diagonal (fun p => (d p : ℂ)) * Wᴴ) (i, i) (j, j)
      = ∑ p : n × n, (d p : ℂ) * W (i, i) p * (starRingEnd ℂ) (W (j, j) p) := by
    intro i j
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Complex.star_def]
    ring
  have key : ∀ p : n × n, ∑ i, ∑ j, ((d p : ℂ) * W (i, i) p * (starRingEnd ℂ) (W (j, j) p))
      = ((d p * Complex.normSq (∑ k, W (k, k) p) : ℝ) : ℂ) := by
    intro p
    calc ∑ i, ∑ j, ((d p : ℂ) * W (i, i) p * (starRingEnd ℂ) (W (j, j) p))
        = ∑ i, ((d p : ℂ) * W (i, i) p * ∑ j, (starRingEnd ℂ) (W (j, j) p)) := by
          simp [Finset.mul_sum]
      _ = (∑ i, (d p : ℂ) * W (i, i) p) * (∑ j, (starRingEnd ℂ) (W (j, j) p)) := by
          rw [Finset.sum_mul]
      _ = (d p : ℂ) * ((∑ i, W (i, i) p) * (starRingEnd ℂ) (∑ j, W (j, j) p)) := by
          rw [← Finset.mul_sum, map_sum]; ring
      _ = ((d p * Complex.normSq (∑ k, W (k, k) p) : ℝ) : ℂ) := by
          push_cast
          rw [Complex.normSq_eq_conj_mul_self]
          ring
  simp only [qform]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => step i j))]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun p _ => key p

/-! ### The lifted multiplication operators -/

/-- Left multiplication by `A`, as a matrix acting on vectorised matrices. -/
