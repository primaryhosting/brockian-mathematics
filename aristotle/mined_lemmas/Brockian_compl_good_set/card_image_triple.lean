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

lemma card_image_triple (p : ℕ) [NeZero p] (h₁ h₂ h₃ : ℤ)
    (h12 : ¬ h₁ ≡ h₂ [ZMOD (p : ℤ)]) (h13 : ¬ h₁ ≡ h₃ [ZMOD (p : ℤ)])
    (h23 : ¬ h₂ ≡ h₃ [ZMOD (p : ℤ)]) :
    ((({h₁, h₂, h₃} : Finset ℤ)).image (fun h : ℤ => (h : ZMod p))).card = 3 := by
  classical
  have e12 : ((h₁ : ZMod p)) ≠ (h₂ : ZMod p) := fun h => h12 ((ZMod.intCast_eq_intCast_iff _ _ _).mp h)
  have e13 : ((h₁ : ZMod p)) ≠ (h₃ : ZMod p) := fun h => h13 ((ZMod.intCast_eq_intCast_iff _ _ _).mp h)
  have e23 : ((h₂ : ZMod p)) ≠ (h₃ : ZMod p) := fun h => h23 ((ZMod.intCast_eq_intCast_iff _ _ _).mp h)
  rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  rw [Finset.card_insert_of_notMem (by simp [e12, e13]),
    Finset.card_insert_of_notMem (by simp [e23]), Finset.card_singleton]

/-- **Constellation local count, `k = 3`.**  If the three shifts are pairwise
incongruent modulo `p`, then exactly `p - 3` residue classes modulo `p` give a
constellation `(a + h₁, a + h₂, a + h₃)` all of whose members are nonzero modulo `p`. -/
