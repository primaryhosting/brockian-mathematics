/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace QI

/-- The `n`-bit state space, an `n`-dimensional vector space over `ZMod 2`. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product `⟪y, x⟫ = ∑ i, y i * x i`. -/

lemma pick_add {n : ℕ} (s x : Vec n) (hs : s ≠ 0) : pick s (x + s) = pick s x := by
  have hxs : x + s + s = x := by rw [add_assoc, vec_add_self, add_zero]
  have hne : x + s ≠ x := fun hcon => hs (by simpa using hcon)
  have hE : (Fintype.equivFin (Vec n)) x ≠ (Fintype.equivFin (Vec n)) (x + s) := fun hcon =>
    hne ((Fintype.equivFin (Vec n)).injective hcon).symm
  rcases lt_or_gt_of_ne hE with h | h
  · rw [pick, pick, hxs, if_pos h.le, if_neg (not_le.mpr h)]
  · rw [pick, pick, hxs, if_neg (not_le.mpr h), if_pos h.le]

