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

lemma key_bound (A X : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) :
    2 * t * rip A X - t ^ 2 * frobSq A ≤ frobSq X := by
  have h0 : 0 ≤ frobSq (X - (t : ℂ) • A) := frobSq_nonneg _
  rw [frobSq_sub, rip_smul, frobSq_smul] at h0
  rw [rip_comm A X]
  nlinarith [h0]

/-! ### Spectral functional calculus for Hermitian matrices -/

section Spec

variable {A : Matrix (Fin d) (Fin d) ℂ}

/-- `specMat hA f` is the matrix `U * diagonal f * Uᴴ` where `U` diagonalizes `A`. -/
