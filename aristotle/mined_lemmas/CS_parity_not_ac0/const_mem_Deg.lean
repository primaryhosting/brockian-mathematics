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

lemma const_mem_Deg {n D : ℕ} (c : F3) : (fun _ => c : Cube n → F3) ∈ Deg n D := by
  have : (fun _ => c : Cube n → F3) = c • (1 : Cube n → F3) := by
    funext x; simp
  rw [this]
  exact Submodule.smul_mem _ _ one_mem_Deg

