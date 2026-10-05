import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `wcost w u l` is the total weight of the walk that starts at `u` and visits the
vertices of `l` in order. -/

lemma settled_all (w : V → V → ℝ≥0∞) (s : V) :
    ((step w)^[Fintype.card V] (init s)).1 = Finset.univ := by
  rcases card_iterate w s (Fintype.card V) with h | h
  · exact h
  · exact Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) h)

/-- **Dijkstra's algorithm is correct**: on a graph with nonnegative weights
(`ℝ≥0∞`-valued, with `⊤` denoting the absence of an edge), the algorithm returns, for
every vertex `v`, the infimum of the weights of all walks from the source `s` to `v`. -/
