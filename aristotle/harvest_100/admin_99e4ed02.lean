/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The *local count* of a `3`-element constellation `h = (h 0, h 1, h 2)` modulo a prime `p`:
the number of residues `n : ZMod p` for which the shifted product `∏ i, (n + h i)` vanishes,
i.e. the number of residue classes that a prime constellation `(n + h 0, n + h 1, n + h 2)`
must avoid modulo `p`. -/
noncomputable def localZeroCount3 (p : ℕ) [Fact p.Prime] (h : Fin 3 → ZMod p) : ℕ :=
  (Finset.univ.filter (fun n : ZMod p => ∏ i, (n + h i) = 0)).card

/-- The set of "bad" residues is exactly the set of negatives of the shifts. -/
lemma filter_prod_eq_zero_eq_image_neg (p : ℕ) [Fact p.Prime] (h : Fin 3 → ZMod p) :
    (Finset.univ.filter (fun n : ZMod p => ∏ i, (n + h i) = 0))
      = ({h 0, h 1, h 2} : Finset (ZMod p)).image (fun x => -x) := by
  ext n
  simp [Fin.prod_univ_three, mul_eq_zero, add_eq_zero_iff_eq_neg, or_assoc]

/-- The local count equals the number of *distinct* shifts modulo `p`. -/
lemma localZeroCount3_eq_card (p : ℕ) [Fact p.Prime] (h : Fin 3 → ZMod p) :
    localZeroCount3 p h = ({h 0, h 1, h 2} : Finset (ZMod p)).card := by
  rw [localZeroCount3, filter_prod_eq_zero_eq_image_neg]
  exact Finset.card_image_of_injective _ neg_injective

/-- The local count of a `3`-constellation is at most `3`. -/
lemma localZeroCount3_le_three (p : ℕ) [Fact p.Prime] (h : Fin 3 → ZMod p) :
    localZeroCount3 p h ≤ 3 := by
  rw [localZeroCount3_eq_card]
  exact le_trans (Finset.card_insert_le _ _)
    (by simpa using Nat.succ_le_succ (Finset.card_insert_le (h 1) {h 2}))

/-- **Constellation local count, `k = 3`.**  For a prime `p` and a triple of shifts
`h : Fin 3 → ZMod p`:

* the number of residues killed by the constellation equals the number of distinct shifts;
* it is at most `3`;
* it is exactly `3` iff the three shifts are pairwise distinct modulo `p`;
* if `p > 3` then some residue survives, i.e. the triple is locally admissible at `p`,
  and in fact at least `p - 3` residues survive. -/
theorem ConstellationLocalCountK3 (p : ℕ) [Fact p.Prime] (h : Fin 3 → ZMod p) :
    localZeroCount3 p h = ({h 0, h 1, h 2} : Finset (ZMod p)).card ∧
    localZeroCount3 p h ≤ 3 ∧
    (localZeroCount3 p h = 3 ↔ (h 0 ≠ h 1 ∧ h 0 ≠ h 2 ∧ h 1 ≠ h 2)) ∧
    (3 < p → ∃ n : ZMod p, ∏ i, (n + h i) ≠ 0) ∧
    p - 3 ≤ (Finset.univ.filter (fun n : ZMod p => ∏ i, (n + h i) ≠ 0)).card := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hsplit :
      localZeroCount3 p h
        + (Finset.univ.filter (fun n : ZMod p => ∏ i, (n + h i) ≠ 0)).card = p := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ZMod p))) (p := fun n : ZMod p => ∏ i, (n + h i) = 0)
    rw [localZeroCount3]
    simpa [hcard] using this
  have htwo : ∀ a b : ZMod p, ({a, b} : Finset (ZMod p)).card ≤ 2 := by
    intro a b
    simpa using Finset.card_insert_le a {b}
  refine ⟨localZeroCount3_eq_card p h, localZeroCount3_le_three p h, ?_, ?_, ?_⟩
  · rw [localZeroCount3_eq_card]
    constructor
    · intro hc
      by_contra hcon
      push_neg at hcon
      have : ({h 0, h 1, h 2} : Finset (ZMod p)).card ≤ 2 := by
        rcases eq_or_ne (h 0) (h 1) with h01 | h01
        · exact le_trans (Finset.card_le_card
            (by simp [h01])) (htwo (h 1) (h 2))
        · rcases eq_or_ne (h 0) (h 2) with h02 | h02
          · exact le_trans (Finset.card_le_card
              (by simp [h02])) (htwo (h 1) (h 2))
          · have h12 := hcon h01 h02
            exact le_trans (Finset.card_le_card
              (by simp [h12])) (htwo (h 0) (h 2))
      omega
    · rintro ⟨h01, h02, h12⟩
      rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
        Finset.card_insert_of_notMem (by simp [h12])]
      simp
  · intro hp
    have hle := localZeroCount3_le_three p h
    have : 0 < (Finset.univ.filter (fun n : ZMod p => ∏ i, (n + h i) ≠ 0)).card := by omega
    obtain ⟨n, hn⟩ := Finset.card_pos.mp this
    exact ⟨n, (Finset.mem_filter.mp hn).2⟩
  · have hle := localZeroCount3_le_three p h
    omega

end Brockian

#print axioms Brockian.ConstellationLocalCountK3

