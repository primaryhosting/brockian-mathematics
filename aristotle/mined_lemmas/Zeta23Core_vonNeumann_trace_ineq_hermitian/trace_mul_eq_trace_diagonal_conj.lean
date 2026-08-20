/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

/-- The matrix of squared absolute values of the entries of a unitary matrix is doubly
stochastic. -/

lemma trace_mul_eq_trace_diagonal_conj {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    Matrix.trace (A * B)
      = Matrix.trace (diagonal (RCLike.ofReal ∘ hA.eigenvalues)
          * (star (hA.eigenvectorUnitary : Matrix n n 𝕜) * (hB.eigenvectorUnitary : Matrix n n 𝕜))
          * diagonal (RCLike.ofReal ∘ hB.eigenvalues)
          * star (star (hA.eigenvectorUnitary : Matrix n n 𝕜)
              * (hB.eigenvectorUnitary : Matrix n n 𝕜))) := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hV
  have hUU : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).1 hA.eigenvectorUnitary.2
  have hUU' : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hA.eigenvectorUnitary.2
  have hAeq := hA.spectral_theorem
  have hBeq := hB.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hAeq hBeq
  rw [← hU] at hAeq
  rw [← hV] at hBeq
  rw [Matrix.star_mul, star_star]
  set Da : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDa
  set Db : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hB.eigenvalues) with hDb
  have key : U * (Da * (star U * V) * Db * (star V * U)) * star U = A * B := by
    rw [hAeq, hBeq]
    simp only [mul_assoc, hUU, mul_one]
  rw [← key, Matrix.trace_mul_comm, ← mul_assoc, hUU', one_mul]

/-- `Re tr(AB) = ∑_{p,q} α_p β_q |W_{pq}|²` where `W` is the unitary connecting the two
eigenbases. -/
