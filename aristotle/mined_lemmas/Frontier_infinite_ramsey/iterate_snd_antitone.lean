import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Frontier

open Classical in
/-- The `U`-generic colour at `n`: the colour `b` such that `{m | c n m = b} ∈ U`. -/

lemma iterate_snd_antitone (c : ℕ → ℕ → Bool) (b : Bool) (p : ℕ × Set ℕ) :
    ∀ {k l : ℕ}, k ≤ l → ((rstep c b)^[l] p).2 ⊆ ((rstep c b)^[k] p).2 := by
  have key : ∀ k : ℕ, ((rstep c b)^[k + 1] p).2 ⊆ ((rstep c b)^[k] p).2 := by
    intro k
    rw [Function.iterate_succ_apply']
    exact rstep_snd_subset c b _
  intro k l hkl
  induction l with
  | zero => simpa using (Nat.le_zero.1 hkl) ▸ subset_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · exact (key n).trans (ih (Nat.lt_succ_iff.1 h))
    · have : k = n + 1 := le_antisymm hkl h
      subst this; exact subset_rfl

/-- **Infinite Ramsey theorem** for pairs and two colours: for every colouring
`c : ℕ → ℕ → Bool` of the pairs of natural numbers there is an infinite set `S`
and a colour `b` such that every pair from `S` gets colour `b`. -/
