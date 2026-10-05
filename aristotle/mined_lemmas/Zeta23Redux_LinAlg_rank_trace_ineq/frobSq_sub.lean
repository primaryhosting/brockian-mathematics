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

lemma frobSq_sub (X Y : Matrix (Fin d) (Fin d) ℂ) :
    frobSq (X - Y) = frobSq X + frobSq Y - 2 * fip X Y := by
  rw [sub_eq_add_neg, frobSq_add]
  have h1 : frobSq (-Y) = frobSq Y := by simp [frobSq]
  have h2 : fip X (-Y) = -fip X Y := by simp [fip]
  rw [h1, h2]; ring

/-! ## Unitary invariance -/

