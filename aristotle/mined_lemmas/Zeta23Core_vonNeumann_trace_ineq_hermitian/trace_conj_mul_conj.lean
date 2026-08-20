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

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Core

open Matrix Finset

/-! ### A rearrangement bound for doubly stochastic matrices -/

/-- If `a` and `b` monovary, then the bilinear form `∑ j k, D j k * (a j * b k)` attached to a
doubly stochastic matrix `D` is at most `∑ i, a i * b i`.  This is the combinatorial heart of the
von Neumann trace inequality: it follows from Birkhoff's theorem together with the rearrangement
inequality. -/

lemma trace_conj_mul_conj (U V Da Db : Matrix n n 𝕜) :
    Matrix.trace ((U * Da * star U) * (V * Db * star V))
      = Matrix.trace (Da * (star U * V) * Db * star (star U * V)) := by
  have h1 : (U * Da * star U) * (V * Db * star V)
      = U * (Da * (star U * V) * Db * star V) := by
    simp [mul_assoc]
  rw [h1, Matrix.trace_mul_comm, Matrix.star_mul, star_star]
  congr 1
  simp [mul_assoc]

/-- The eigenvalue functions of two Hermitian matrices monovary, since both are obtained from
antitone functions by the same reindexing. -/
