/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Core

open Matrix Finset

section Weights

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The entrywise squared-modulus matrix `j k ↦ ‖W j k‖ ^ 2` of a matrix `W`. -/

lemma trace_mul_eq_sum {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace =
      ((∑ j, ∑ k, hA.eigenvalues j * hB.eigenvalues k *
        ‖((star (hA.eigenvectorUnitary : Matrix n n 𝕜) *
          (hB.eigenvectorUnitary : Matrix n n 𝕜)) j k)‖ ^ 2 : ℝ) : 𝕜) := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hV
  set Da : Matrix n n 𝕜 := Matrix.diagonal ((RCLike.ofReal ∘ hA.eigenvalues : n → 𝕜)) with hDa
  set Db : Matrix n n 𝕜 := Matrix.diagonal ((RCLike.ofReal ∘ hB.eigenvalues : n → 𝕜)) with hDb
  have hstarW : star (star U * V) = star V * U := by
    rw [Matrix.star_mul, star_star]
  have e1 : A * B = U * (Da * (star U * V * Db * star V)) := by
    conv_lhs => rw [hA.spectral_theorem, hB.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    noncomm_ring
  have e2 : (A * B).trace = (Da * ((star U * V) * Db * star (star U * V))).trace := by
    rw [e1, Matrix.trace_mul_comm, hstarW]
    congr 1
    noncomm_ring
  rw [e2, trace_diagonal_conj hA.eigenvalues hB.eigenvalues (star U * V)]

end Trace

/-- **Von Neumann trace inequality, Hermitian case.**
For Hermitian matrices `A`, `B` over an `RCLike` field indexed by a finite type,
the real part of `trace (A * B)` is at most `∑ i, a i * b i`, where `a` and `b` are the
eigenvalues of `A` and `B` listed in decreasing order (`Matrix.IsHermitian.eigenvalues₀`,
which is antitone by `Matrix.IsHermitian.eigenvalues₀_antitone`). -/
