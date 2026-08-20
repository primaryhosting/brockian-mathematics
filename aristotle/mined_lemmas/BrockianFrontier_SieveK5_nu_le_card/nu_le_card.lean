import Mathlib
namespace BrockianFrontier.SieveK5

/-- Residues covered by `G` mod `p`. -/

lemma nu_le_card (G : Finset ℕ) (p : ℕ) : nu G p ≤ G.card :=
  Finset.card_image_le

/-- General positivity criterion: if `G` misses a residue class modulo every prime
    `q ≤ G.card`, then all its local factors are positive.  (For `q > G.card` the
    gap-set cannot cover all residues, since `nu G q ≤ G.card < q`.) -/
