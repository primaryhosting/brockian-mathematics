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

lemma card_image_neg_cast (p : ℕ) [NeZero p] (H : Finset ℤ) :
    (H.image (fun h : ℤ => -(h : ZMod p))).card = (H.image (fun h : ℤ => (h : ZMod p))).card := by
  classical
  have : H.image (fun h : ℤ => -(h : ZMod p))
      = (H.image (fun h : ℤ => (h : ZMod p))).image (fun x : ZMod p => -x) := by
    rw [Finset.image_image]
    rfl
  rw [this, Finset.card_image_of_injective _ neg_injective]

/-- **General local count formula.**  `localCount p H = p - #(H mod p)`. -/
