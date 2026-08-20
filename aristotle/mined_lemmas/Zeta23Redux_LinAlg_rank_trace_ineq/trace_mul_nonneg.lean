import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators ComplexOrder

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The real part of the trace of a matrix. -/

lemma trace_mul_nonneg {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  set U := (hA.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hA' : A = U * Matrix.diagonal (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hA.1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rfl
  have hM : ((Uᴴ * B * U)).PosSemidef := hB.conjTranspose_mul_mul_same U
  have htr : Matrix.trace (A * B)
      = Matrix.trace (Matrix.diagonal (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)) *
          (Uᴴ * B * U)) := by
    conv_lhs => rw [hA']
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hsum : Matrix.trace (Matrix.diagonal (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)) *
      (Uᴴ * B * U)) = ∑ i, ((hA.1.eigenvalues i : ℝ) : ℂ) * (Uᴴ * B * U) i i := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  rw [htr, hsum, Complex.re_sum]
  refine Finset.sum_nonneg (fun i _ => ?_)
  have h1 : 0 ≤ hA.1.eigenvalues i := hA.eigenvalues_nonneg i
  have h2 : 0 ≤ ((Uᴴ * B * U) i i).re := (Complex.le_def.mp hM.diag_nonneg).1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  positivity

/-! ### The rank-trace inequality -/

/-- **The rank-trace inequality (Lemma 3.2).** For Hermitian `P, Q` with `P` positive
semidefinite of rank at most `r` and `Q` having at most `b` strictly positive eigenvalues,
and any `c > 0`,
`c * tr P - (c²/4) * r + 2c * tr Q - c² * b ≤ ‖P + Q‖²_F`. -/
