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

section DoublyStochastic

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Two antitone functions monovary. -/

theorem trace_mul_eq_sum_sq_norm {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ W : Matrix n n 𝕜, W * star W = 1 ∧ star W * W = 1 ∧
      trace (A * B) =
        RCLike.ofReal (∑ j, ∑ k, hA.eigenvalues j * hB.eigenvalues k * ‖W j k‖ ^ 2) := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hVdef
  have hU1 : U * star U = 1 := by
    rw [hUdef]; exact_mod_cast Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hU2 : star U * U = 1 := by
    rw [hUdef]; exact_mod_cast Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hV1 : V * star V = 1 := by
    rw [hVdef]; exact_mod_cast Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2
  have hV2 : star V * V = 1 := by
    rw [hVdef]; exact_mod_cast Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.2
  set Da : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDa
  set Db : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hB.eigenvalues) with hDb
  have hAeq : A = U * Da * star U := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have hBeq : B = V * Db * star V := by
    conv_lhs => rw [hB.spectral_theorem, Unitary.conjStarAlgAut_apply]
  refine ⟨star U * V, ?_, ?_, ?_⟩
  · rw [Matrix.star_mul, star_star]
    calc star U * V * (star V * U) = star U * (V * star V) * U := by
          simp only [mul_assoc]
      _ = 1 := by rw [hV1, mul_one, hU2]
  · calc star (star U * V) * (star U * V) = star V * (U * star U) * V := by
          rw [Matrix.star_mul, star_star]; simp only [mul_assoc]
      _ = 1 := by rw [hU1, mul_one, hV2]
  · rw [← trace_diagonal_mul_mul_diagonal_mul_star]
    have hstar : star (star U * V) = star V * U := by rw [Matrix.star_mul, star_star]
    rw [hstar, ← hDa, ← hDb]
    have hconj : U * (Da * (star U * V) * (Db * (star V * U))) * star U = A * B := by
      rw [hAeq, hBeq]
      simp only [mul_assoc, hU1, mul_one]
    rw [← hconj]
    rw [mul_assoc, trace_mul_comm]
    simp only [mul_assoc, hU2, mul_one]

end Trace

section Sorted

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The eigenvalues of a Hermitian matrix indexed by `Fin n`, listed in decreasing order. -/
