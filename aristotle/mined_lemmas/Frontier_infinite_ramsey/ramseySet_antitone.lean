/-
/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

namespace Frontier

open Filter Set

/-- A fixed nonprincipal ultrafilter on `ℕ`: an ultrafilter refining the cofinite filter. -/

lemma ramseySet_antitone (c : ℕ → ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    ramseySet c n ⊆ ramseySet c m := by
  induction n with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hm | hm
      · have : ramseySet c (n + 1) ⊆ ramseySet c n := by
          rw [ramseySet_succ, ramseyStep]
          exact fun y hy => hy.1.1
        exact this.trans (ih (Nat.lt_succ_iff.mp hm))
      · have : m = n + 1 := le_antisymm h hm
        subst this; exact subset_rfl

