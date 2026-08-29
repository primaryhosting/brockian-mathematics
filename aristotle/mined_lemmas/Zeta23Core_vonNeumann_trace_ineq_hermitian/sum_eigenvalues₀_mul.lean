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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Finset Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared moduli of the entries of `W`. If `W` is unitary this is a doubly
stochastic matrix. -/

lemma sum_eigenvalues₀_mul {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i
      = ∑ i : n, hA.eigenvalues i * hB.eigenvalues i := by
  unfold Matrix.IsHermitian.eigenvalues
  rw [← Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm
    (fun j => hA.eigenvalues₀ j * hB.eigenvalues₀ j)]

/-- **Von Neumann trace inequality, Hermitian case.**
For Hermitian matrices `A`, `B` over an `RCLike` field, the real part of `tr (A * B)` is at most
the sum of the products of their eigenvalues, each sorted in decreasing order.  Decreasing
sortedness is expressed by using `Matrix.IsHermitian.eigenvalues₀`, which is antitone (see
`Matrix.IsHermitian.eigenvalues₀_antitone`). -/
