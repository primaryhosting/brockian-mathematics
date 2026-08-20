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

lemma ramsey_34_card {c : ℕ → ℕ → Bool} (hsym : ∀ x y, c x y = c y x) {s : Finset ℕ}
    (hcard : s.card = 9) : Arrows c s 3 4 := by
  by_contra hcon
  rw [Arrows, not_or] at hcon
  obtain ⟨h3, h4⟩ := hcon
  push_neg at h3 h4
  have hdeg : ∀ v ∈ s, (Nbr c s v true).card = 3 := by
    intro v hv
    have hsplit := card_Nbr_add c hv
    have hR : (Nbr c s v true).card ≤ 3 := by
      by_contra hR
      push_neg at hR
      have h4le : (4 : ℕ) ≤ (Nbr c s v true).card := hR
      rcases arrow_two_left hsym h4le with ⟨t, hts, hc2, hmono⟩ | ⟨t, hts, hc4, hmono⟩
      · obtain ⟨t', ht's, hcard', hmono'⟩ := extend hsym hv hts hmono
        exact absurd hmono' (h3 t' ht's (by omega))
      · exact absurd hmono (h4 t (hts.trans Nbr_subset) hc4)
    have hB : (Nbr c s v false).card ≤ 5 := by
      by_contra hB
      push_neg at hB
      have h6le : (6 : ℕ) ≤ (Nbr c s v false).card := hB
      rcases ramsey_33 hsym h6le with ⟨t, hts, hc3, hmono⟩ | ⟨t, hts, hc3, hmono⟩
      · exact absurd hmono (h3 t (hts.trans Nbr_subset) hc3)
      · obtain ⟨t', ht's, hcard', hmono'⟩ := extend hsym hv hts hmono
        exact absurd hmono' (h4 t' ht's (by omega))
    omega
  have hsum : ∑ v ∈ s, (Nbr c s v true).card = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hcard, smul_eq_mul]
  have heven := even_sum_deg c hsym s
  rw [hsum] at heven
  exact (by decide : ¬ Even 27) heven

/-- `R(3,4) ≤ 9`, monotone form. -/
