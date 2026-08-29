import Mathlib

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators

namespace CS

/-- The field with three elements. -/
abbrev F3 := ZMod 3

/-- The Boolean cube on `n` coordinates. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- `±1` encoding of a Boolean value inside `F3`. -/

lemma one_mem_Deg {n D : ℕ} : (1 : Cube n → F3) ∈ Deg n D := by
  have := mono_mem_Deg (A := (∅ : Finset (Fin n))) (D := D) (by simp)
  simpa using this

