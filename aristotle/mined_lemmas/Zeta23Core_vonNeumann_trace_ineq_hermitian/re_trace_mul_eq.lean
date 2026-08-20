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

lemma re_trace_mul_eq {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (Matrix.trace (A * B))
      = ∑ p, ∑ q, hA.eigenvalues p * hB.eigenvalues q *
          ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *
            (hB.eigenvectorUnitary : Matrix n n 𝕜)) p q‖ ^ 2 := by
  rw [trace_mul_eq_trace_diagonal_conj hA hB, trace_diagonal_conj, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun q _ => RCLike.ofReal_re _

/-- Two antitone functions monovary. -/
