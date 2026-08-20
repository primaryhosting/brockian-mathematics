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

For a finite set of integer shifts `H = {h₁, …, h_k}` (a *constellation pattern*) and a
modulus `p`, the *local count* is the number of residue classes `a` mod `p` such that all
the shifted values `a + hᵢ` are nonzero mod `p`; this is the local factor appearing in the
Hardy–Littlewood singular series for prime constellations.

The general formula `localCount p H = p - #(H mod p)` is proved as `Brockian.localCount_eq`
(via `Finset.card_compl`, `Finset.card_image_of_injective` and `neg_injective`), and the
main result specialises it to `k = 3`.
-/

namespace Brockian

open Finset

/-- The local count of an integer constellation `H = {h₁, …, h_k}` at the modulus `p`:
the number of residues `a` modulo `p` for which none of the shifted values `a + hᵢ`
vanishes modulo `p`. -/

lemma localCount_eq (p : ℕ) [NeZero p] (H : Finset ℤ) :
    localCount p H = p - (H.image (fun h : ℤ => (h : ZMod p))).card := by
  classical
  have hcompl := congrArg Finset.card (compl_good_set p H)
  rw [Finset.card_compl, ZMod.card, card_image_neg_cast] at hcompl
  have hle : (H.image (fun h : ℤ => (h : ZMod p))).card ≤ p := by
    calc (H.image (fun h : ℤ => (h : ZMod p))).card
        ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = p := by rw [Finset.card_univ, ZMod.card]
  have hlc : localCount p H ≤ p := by
    unfold localCount
    calc (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + (h : ZMod p) ≠ 0)).card
        ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = p := by rw [Finset.card_univ, ZMod.card]
  unfold localCount at *
  omega

/-- The reduction mod `p` of a three-element constellation has exactly three elements
when the shifts are pairwise incongruent. -/
