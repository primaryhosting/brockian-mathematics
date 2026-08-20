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

theorem sortedEigenvalues_eq_comp {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    sortedEigenvalues hA = hA.eigenvalues ∘ Tuple.sort (fun i => -(hA.eigenvalues i)) := rfl

