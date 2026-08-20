/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
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

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/

lemma sortedEigenvalues_eq_comp_perm {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    ∃ sg : Equiv.Perm (Fin d), ∀ i, sortedEigenvalues hA i = hA.eigenvalues (sg i) := by
  refine ⟨(finCongr (Fintype.card_fin d).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin _)), fun i => ?_⟩
  simp [sortedEigenvalues, Matrix.IsHermitian.eigenvalues]

/-- **Von Neumann's trace inequality**, stated with the eigenvalues of both matrices listed in
decreasing order. -/
