import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-! ## Unconditional base cases -/

/-- A finite group whose order is squarefree is solvable (it is a Z-group). -/

theorem isSolvable_of_isPrimePow_card (G : Type u) [Group G] [Finite G]
    (h : IsPrimePow (Nat.card G)) : IsSolvable G := by
  obtain ⟨p, k, hp, hk, hpk⟩ := h
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  haveI : Fact p.Prime := ⟨hp'⟩
  have hP : IsPGroup p G := IsPGroup.of_card hpk.symm
  have := hP.isNilpotent
  infer_instance

/-- Every odd number below `45` is either squarefree or a prime power. -/
