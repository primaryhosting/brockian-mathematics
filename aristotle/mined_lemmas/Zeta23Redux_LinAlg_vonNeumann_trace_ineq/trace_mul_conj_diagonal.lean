/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Matrix Finset

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/

lemma trace_mul_conj_diagonal (alpha beta : Fin d → ℝ)
    {U V : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.trace ((U * Matrix.diagonal (fun i => (alpha i : ℂ)) * star U) *
        (V * Matrix.diagonal (fun i => (beta i : ℂ)) * star V))
      = ((∑ p, ∑ q, alpha p * beta q * Complex.normSq ((star U * V) p q) : ℝ) : ℂ) := by
  set Da := Matrix.diagonal (fun i => (alpha i : ℂ)) with hDa
  set Db := Matrix.diagonal (fun i => (beta i : ℂ)) with hDb
  set W := star U * V with hW
  have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hstarW : star W = star V * U := by
    rw [hW, Matrix.star_mul, star_star]
  have hfact : (U * Da * star U) * (V * Db * star V) = U * (Da * W * Db * star W) * star U := by
    rw [hstarW, hW]
    have h1 : U * (Da * (star U * V) * Db * (star V * U)) * star U
        = U * Da * (star U * V) * Db * (star V * (U * star U)) := by
      simp [mul_assoc]
    rw [h1, hUU, mul_one]
    simp [mul_assoc]
  rw [hfact, Matrix.trace_mul_comm, ← mul_assoc,
    show star U * U = 1 from Matrix.mem_unitaryGroup_iff'.mp hU, one_mul]
  have hentry : ∀ p, (Da * W * Db * star W) p p
      = ((∑ q, alpha p * beta q * Complex.normSq (W p q) : ℝ) : ℂ) := by
    intro p
    rw [Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_apply, Complex.star_def,
      ← Complex.mul_conj]
    ring
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, hentry]
  push_cast
  rfl

/-- **Von Neumann's trace inequality** for Hermitian matrices: if `mu` and `nu` list the
eigenvalues of the Hermitian matrices `A` and `B` in decreasing order, then
`Re (trace (A * B)) ≤ ∑ i, mu i * nu i`. -/
