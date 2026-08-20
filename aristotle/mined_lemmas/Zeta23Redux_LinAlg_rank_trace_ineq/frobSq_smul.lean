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

lemma frobSq_smul (A : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) :
    frobSq ((t : ℂ) • A) = t ^ 2 * frobSq A := by
  have h : ((t : ℂ) • A)ᴴ * ((t : ℂ) • A) = ((t ^ 2 : ℝ) : ℂ) • (Aᴴ * A) := by
    rw [Matrix.conjTranspose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def,
      Complex.conj_ofReal]
    push_cast
    ring_nf
  unfold frobSq
  rw [h, Matrix.trace_smul]
  simp [-Complex.ofReal_pow]

/-- The basic quadratic bound: `‖X‖² ≥ 2⟨A,X⟩ - ‖A‖²`, scaled by a real parameter `t`. -/
