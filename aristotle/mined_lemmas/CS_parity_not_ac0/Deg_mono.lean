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

lemma Deg_mono {n : ℕ} {D E : ℕ} (h : D ≤ E) : Deg n D ≤ Deg n E := by
  apply Submodule.span_le.2
  rintro f ⟨A, hA, rfl⟩
  exact mono_mem_Deg (hA.trans h)

