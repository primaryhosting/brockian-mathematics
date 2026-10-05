/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

variable {α : Type*} [PartialOrder α]

/-- The finset of all chains (as finsets) contained in a given finset `t`. -/

theorem dilworth (α : Type*) [PartialOrder α] [Fintype α] :
    minAntichainCover α = longestChain α := by
  classical
  obtain ⟨F, hF, hFcard⟩ := exists_antichain_cover (α := α)
  have hmem : F.card ∈ {n : ℕ | ∃ F : Finset (Finset α), IsAntichainCover F ∧ F.card = n} :=
    ⟨F, hF, rfl⟩
  have hle : minAntichainCover α ≤ longestChain α :=
    le_trans (Nat.sInf_le hmem) hFcard
  have hne : {n : ℕ | ∃ F : Finset (Finset α), IsAntichainCover F ∧ F.card = n}.Nonempty :=
    ⟨F.card, hmem⟩
  obtain ⟨G, hG, hGcard⟩ := Nat.sInf_mem hne
  have hge : longestChain α ≤ minAntichainCover α := by
    rw [minAntichainCover, ← hGcard]
    exact longestChain_le_card_of_cover hG
  omega

end Math

