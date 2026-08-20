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

The proof follows the classical route: writing `A = U Dα U*`, `B = V Dβ V*` via the spectral
theorem, one gets `tr (A B) = ∑ j k, α j * β k * |W j k|²` for the unitary `W = U* V`.
The matrix of squared moduli of a unitary matrix is doubly stochastic, so by Birkhoff's theorem
(`exists_eq_sum_perm_of_mem_doublyStochastic`) the right-hand side is a convex combination of the
quantities `∑ j, α j * β (σ j)`, each of which is bounded by `∑ i, a i * b i` by the rearrangement
inequality (`Monovary.sum_mul_comp_perm_le_sum_mul`).
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared absolute values of the entries of a matrix. -/

lemma exists_doublyStochastic_trace_eq {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    ∃ S ∈ doublyStochastic ℝ n,
      RCLike.re (trace (A * B))
        = ∑ j, ∑ k, hA.eigenvalues j * hB.eigenvalues k * S j k := by
  set U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary with hUdef
  set V : Matrix n n 𝕜 := ↑hB.eigenvectorUnitary with hVdef
  have hU1 : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hU2 : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hV1 : star V * V = 1 := Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.2
  have hV2 : V * star V = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2
  set Da : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDa
  set Db : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hB.eigenvalues) with hDb
  have hA' : A = U * Da * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, mul_assoc, hDa, hUdef]
  have hB' : B = V * Db * star V := by
    conv_lhs => rw [hB.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, mul_assoc, hDb, hVdef]
  set W : Matrix n n 𝕜 := star U * V with hW
  have hstarW : star W = star V * U := by rw [hW, Matrix.star_mul, star_star]
  have hW1 : W * star W = 1 := by
    rw [hW, hstarW, mul_assoc, ← mul_assoc V, hV2, one_mul, hU1]
  have hW2 : star W * W = 1 := by
    rw [hW, hstarW, mul_assoc, ← mul_assoc U, hU2, one_mul, hV1]
  refine ⟨weightMatrix W, weightMatrix_mem_doublyStochastic hW1 hW2, ?_⟩
  have htr : trace (A * B) = trace (Da * W * Db * star W) := by
    have hprod : A * B = U * (Da * W * Db * star W) * star U := by
      rw [hA', hB', hW, hstarW]
      simp only [mul_assoc, hU2, mul_one]
    rw [hprod, trace_mul_comm, ← mul_assoc, hU1, one_mul]
  rw [htr, hDa, hDb, trace_diagonal_conj, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by simp [weightMatrix]

omit [DecidableEq n] in
/-- Rearrangement step: for decreasing rearrangements `a`, `b` of `f`, `g`, and any permutation
`σ`, `∑ j, f j * g (σ j) ≤ ∑ i, a i * b i`. -/
