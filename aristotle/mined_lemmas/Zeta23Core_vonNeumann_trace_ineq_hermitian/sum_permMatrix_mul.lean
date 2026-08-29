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

lemma sum_permMatrix_mul (a b : ι → ℝ) (σ : Equiv.Perm ι) :
    ∑ j, ∑ k, (σ.permMatrix ℝ) j k * (a j * b k) = ∑ j, a j * b (σ j) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Finset.sum_ite_eq]

/-- Rearrangement inequality over doubly stochastic matrices: if `a` and `b` monovary, the
weighted sum `∑ j k, P j k * (a j * b k)` over a doubly stochastic `P` is at most
`∑ i, a i * b i`. -/
