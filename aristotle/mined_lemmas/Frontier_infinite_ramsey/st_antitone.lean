import Mathlib
/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter Set


private lemma st_antitone {j k : ℕ} (h : j ≤ k) : (st c i A k).2 ⊆ (st c i A j).2 := by
  induction k, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ k _ ih =>
      refine subset_trans ?_ ih
      intro m hm
      simp only [st, step] at hm
      exact hm.1

