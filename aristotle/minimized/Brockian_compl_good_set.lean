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

lemma compl_good_set (p : ℕ) [NeZero p] (H : Finset ℤ) :
    (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + (h : ZMod p) ≠ 0))ᶜ
      = H.image (fun h : ℤ => -(h : ZMod p)) := by
  classical
  ext a
  simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    not_forall, not_not]
  constructor
  · rintro ⟨h, hH, ha⟩
    exact ⟨h, hH, by linear_combination -ha⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by ring⟩

/-- Negating does not change the number of distinct reductions of the shifts. -/
