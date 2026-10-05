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

lemma hermitian_entry (hA : A.IsHermitian) (i j : n) :
    A i j = ∑ k, ((hA.eigenvalues k : 𝕜)) *
      ((hA.eigenvectorUnitary : Matrix n n 𝕜) i k *
        (starRingEnd 𝕜) ((hA.eigenvectorUnitary : Matrix n n 𝕜) j k)) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
    RCLike.star_def, mul_comm, mul_assoc, mul_left_comm]

/-- `tr (A * B) = ∑_{jk} |W_{jk}|² a_j b_k`, in particular it is real. -/
