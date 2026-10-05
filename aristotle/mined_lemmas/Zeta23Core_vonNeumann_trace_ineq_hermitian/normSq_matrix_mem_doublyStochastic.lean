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

theorem normSq_matrix_mem_doublyStochastic {W : Matrix n n 𝕜}
    (hW1 : W * star W = 1) (hW2 : star W * W = 1) :
    (Matrix.of fun j k => ‖W j k‖ ^ 2) ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  exact ⟨fun i j => sq_nonneg _, fun i => row_sum_normSq_of_unitary hW1 i,
    fun j => col_sum_normSq_of_unitary hW2 j⟩

/-- **Von Neumann trace inequality, Hermitian case.**  For Hermitian matrices `A` and `B` over an
`RCLike` field, the real part of `trace (A * B)` is bounded by the sum of the products of the
eigenvalues of `A` and `B`, each sorted in decreasing order (`Matrix.IsHermitian.eigenvalues₀` is
antitone, see `Matrix.IsHermitian.eigenvalues₀_antitone`). -/
