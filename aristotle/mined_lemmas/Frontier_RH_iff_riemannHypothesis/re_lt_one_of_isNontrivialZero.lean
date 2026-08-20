import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open Complex

/-- A *trivial zero* of the Riemann zeta function is one of the points `-2, -4, -6, …`. -/

theorem re_lt_one_of_isNontrivialZero {s : ℂ} (hs : IsNontrivialZero s) : s.re < 1 := by
  by_contra h
  exact zeta_ne_zero_of_one_le_re (le_of_not_gt h) hs.1

/-- **The critical strip.** Every nontrivial zero of `ζ` lies in the open strip `0 < Re s < 1`. -/
