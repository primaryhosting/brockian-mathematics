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

theorem vonNeumann_trace_ineq_sorted {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A * B)).re ≤ ∑ i, sortedEigenvalues hA i * sortedEigenvalues hB i :=
  vonNeumann_trace_ineq hA hB _ _ (sortedEigenvalues_antitone hA) (sortedEigenvalues_antitone hB)
    (sortedEigenvalues_eq_comp_perm hA) (sortedEigenvalues_eq_comp_perm hB)

end Zeta23Redux.LinAlg

