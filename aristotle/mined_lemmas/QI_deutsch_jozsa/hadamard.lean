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

noncomputable def hadamard (psi : (Fin n → Bool) → ℂ) : (Fin n → Bool) → ℂ :=
  fun y => (1 / (Real.sqrt (2 ^ n) : ℝ)) * ∑ x : Fin n → Bool, (∏ i, sgn (x i && y i)) * psi x

/-- The state of the query register after the phase oracle for `f` has acted on
the uniform superposition. -/
