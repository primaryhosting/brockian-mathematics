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

noncomputable def uniform (n : ℕ) : (Fin n → Bool) → ℂ :=
  fun _ => 1 / (Real.sqrt (2 ^ n) : ℝ)

/-- The `n`-fold Hadamard transform:
`H^{⊗n} ψ (y) = 2^{-n/2} ∑ₓ (-1)^{⟨x,y⟩} ψ x`, where the sign `(-1)^{⟨x,y⟩}` is
written as the product `∏ᵢ (-1)^{xᵢ ∧ yᵢ}`. -/
