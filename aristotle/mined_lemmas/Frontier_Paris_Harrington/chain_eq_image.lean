import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Frontier

/-! ## Basic notions -/

/-- A finite set of naturals is *relatively large* when it is nonempty and its cardinality
is at least its least element. -/

theorem chain_eq_image (n : ℕ) :
    chain U D k n = (Finset.range n).image (chainElt U D k) := by
  induction n with
  | zero => simp [chain]
  | succ n ih => rw [chain_succ, ih, Finset.range_add_one, Finset.image_insert]

/-- Every `j`-element subset of the constructed set gets the colour `D k ∅`
(with the appropriate index `i`, where `i + j = k`). -/
