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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace Frontier

/-- The trivial zeros of the Riemann zeta function: the negative even integers
`-2, -4, -6, …`. -/

theorem re_neg_of_isTrivialZero {s : ℂ} (h : IsTrivialZero s) : s.re < 0 := by
  obtain ⟨n, rfl⟩ := h
  have hc : ((-2 : ℂ) * ((n : ℂ) + 1)) = ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [hc, Complex.ofReal_re]
  have : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg
  linarith

/-- The nontrivial zeros of `ζ` all lie in the open critical strip `0 < re s < 1`. -/
