import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Ramsey

/-- A `b`-monochromatic set of vertices for the edge colouring `c`. -/

lemma ramsey_33 {c : ℕ → ℕ → Bool} (hsym : ∀ x y, c x y = c y x) {s : Finset ℕ}
    (hcard : 6 ≤ s.card) : Arrows c s 3 3 := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hne
  have hsplit := card_Nbr_add c hv
  by_cases hR : 3 ≤ (Nbr c s v true).card
  · rcases arrow_two_left hsym hR with ⟨t, hts, hcard2, hmono⟩ | ⟨t, hts, hcard3, hmono⟩
    · obtain ⟨t', ht's, hcard', hmono'⟩ := extend hsym hv hts hmono
      exact Or.inl ⟨t', ht's, by omega, hmono'⟩
    · exact Or.inr ⟨t, hts.trans Nbr_subset, hcard3, hmono⟩
  · have hB : 3 ≤ (Nbr c s v false).card := by omega
    rcases arrow_two_right hsym hB with ⟨t, hts, hcard3, hmono⟩ | ⟨t, hts, hcard2, hmono⟩
    · exact Or.inl ⟨t, hts.trans Nbr_subset, hcard3, hmono⟩
    · obtain ⟨t', ht's, hcard', hmono'⟩ := extend hsym hv hts hmono
      exact Or.inr ⟨t', ht's, by omega, hmono'⟩

/-- Handshake lemma: the sum of the red degrees is even. -/
