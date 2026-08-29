import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Unitary

variable {d : ℕ}

/-! ## Basic real-valued trace functionals -/

/-- The real part of the trace of a matrix. -/

lemma unit_mul_star (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 :=
  mul_eq_one_comm.mp (unit_star_mul hA)

