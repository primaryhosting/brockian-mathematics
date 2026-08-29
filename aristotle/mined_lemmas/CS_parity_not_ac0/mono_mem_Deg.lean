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

lemma mono_mem_Deg {n D : ℕ} {A : Finset (Fin n)} (h : A.card ≤ D) : mono A ∈ Deg n D :=
  Submodule.subset_span ⟨A, h, rfl⟩

