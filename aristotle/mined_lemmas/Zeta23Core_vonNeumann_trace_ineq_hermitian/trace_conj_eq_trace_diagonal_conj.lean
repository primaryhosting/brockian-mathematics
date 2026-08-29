import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option grind.warning false

namespace Zeta23Core

open Matrix Finset

/-- Two antitone functions on a linear order monovary. -/

theorem trace_conj_eq_trace_diagonal_conj {U V : Matrix n n 𝕜}
    (hUs : U * star U = 1) (hsU : star U * U = 1) (Da Db : Matrix n n 𝕜) :
    Matrix.trace ((U * Da * star U) * (V * Db * star V))
      = Matrix.trace (Da * (star U * V) * Db * star (star U * V)) := by
  have hform : (U * Da * star U) * (V * Db * star V)
      = U * (Da * (star U * V) * Db * star (star U * V)) * star U := by
    simp only [Matrix.star_mul, star_star, Matrix.mul_assoc, hUs, Matrix.mul_one]
  rw [hform, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hsU, Matrix.one_mul]

/-- The row sums of squared moduli of a unitary matrix are `1`. -/
