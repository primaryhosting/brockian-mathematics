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


private lemma st_colour (k : ℕ) :
    (st c i A (k + 1)).2 ⊆ {m | c ((st c i A (k + 1)).1) m = i} := by
  intro m hm
  simp only [st, step] at hm ⊢
  exact hm.2

/-- **Infinite Ramsey theorem** for pairs and two colours: for every 2-colouring `c`
of the (unordered) pairs of natural numbers there is an infinite set `S ⊆ ℕ` and a
colour `i` such that every pair from `S` receives colour `i`. -/
