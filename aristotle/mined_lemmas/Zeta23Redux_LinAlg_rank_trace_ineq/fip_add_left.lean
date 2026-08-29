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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix
open scoped ComplexOrder

variable {d : ℕ}

/-! ## Basic real-valued trace functionals -/

/-- The real part of the trace. -/

lemma fip_add_left (X Y Z : Matrix (Fin d) (Fin d) ℂ) :
    fip (X + Y) Z = fip X Z + fip Y Z := by
  simp [fip, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add]

