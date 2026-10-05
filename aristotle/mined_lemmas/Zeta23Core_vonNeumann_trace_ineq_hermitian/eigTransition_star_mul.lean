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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Finset Matrix

section Rearrangement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Value of the bilinear form `M ↦ ∑ j, ∑ k, M j k * (a j * b k)` at a permutation matrix. -/

lemma eigTransition_star_mul (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (star (eigTransition hA hB)) * eigTransition hA hB = 1 := by
  have hU : (hA.eigenvectorUnitary : Matrix n n 𝕜) * star (hA.eigenvectorUnitary : Matrix n n 𝕜)
      = 1 := mul_eq_one_comm.mp (UnitaryGroup.star_mul_self _)
  have hV : star (hB.eigenvectorUnitary : Matrix n n 𝕜) * (hB.eigenvectorUnitary : Matrix n n 𝕜)
      = 1 := UnitaryGroup.star_mul_self _
  simp only [eigTransition, Matrix.star_mul, star_star]
  rw [mul_assoc, ← mul_assoc (hA.eigenvectorUnitary : Matrix n n 𝕜), hU, one_mul, hV]

