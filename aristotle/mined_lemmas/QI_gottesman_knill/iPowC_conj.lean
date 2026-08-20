/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Bit strings and phases -/

/-- The computational basis of `n` qubits is indexed by bit strings `Fin n → ZMod 2`. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The `𝔽₂`-valued inner product of two bit strings. -/

lemma iPowC_conj (t : ZMod 4) : star (iPowC t) = iPowC (-t) := by
  have h4 : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by revert t; decide
  rcases h4 with h | h | h | h <;> subst h <;>
    simp [iPowC_zero, iPowC_one, iPowC_two, iPowC_three,
      show -(0 : ZMod 4) = 0 from by decide, show -(1 : ZMod 4) = 3 from by decide,
      show -(2 : ZMod 4) = 2 from by decide, show -(3 : ZMod 4) = 1 from by decide]

