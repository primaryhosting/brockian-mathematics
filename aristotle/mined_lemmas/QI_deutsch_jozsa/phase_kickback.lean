import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

/-! ## Setup

We model the Deutsch–Jozsa algorithm on `n` query bits.  A computational basis
state is an element of `Fin n → Bool`, and a (pure) state of the query register
is a function `(Fin n → Bool) → ℂ` of amplitudes. -/

variable {n : ℕ}

/-- The sign `(-1)^b` attached to a Boolean value. -/

theorem phase_kickback (f : (Fin n → Bool) → Bool) :
    xorOracle f (fun p => uniform n p.1 * minusState p.2)
      = fun p => phaseOracleState f p.1 * minusState p.2 := by
  funext p
  obtain ⟨x, b⟩ := p
  cases b <;> cases hfx : f x <;>
    simp [xorOracle, minusState, phaseOracleState, sgn, hfx]

/-! ## Auxiliary lemmas -/

