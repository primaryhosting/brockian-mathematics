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

def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ ¬ IsTrivialZero s ∧ s ≠ 1

/-- The Riemann Hypothesis: every nontrivial zero of `ζ` has real part `1/2`.
This is equivalent to Mathlib's `RiemannHypothesis`, see `RH_iff_riemannHypothesis`. -/
