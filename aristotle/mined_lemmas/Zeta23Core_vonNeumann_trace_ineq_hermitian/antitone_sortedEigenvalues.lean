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

theorem antitone_sortedEigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    Antitone (sortedEigenvalues hA) := by
  have h := Tuple.monotone_sort (fun i => -(hA.eigenvalues i))
  intro i j hij
  have := h hij
  simpa [sortedEigenvalues, Function.comp] using this

end Sorted

section Main

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Von Neumann trace inequality, Hermitian case.**
If `A` and `B` are Hermitian matrices over an `RCLike` field, indexed by a finite linearly
ordered type, and `a`, `b` are the eigenvalue lists of `A` and `B` respectively, each
rearranged into decreasing order, then `Re (tr (A * B)) ≤ ∑ i, a i * b i`. -/
