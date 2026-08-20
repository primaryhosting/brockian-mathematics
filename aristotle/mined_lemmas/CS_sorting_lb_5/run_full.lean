import Mathlib

/-!
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- An input to a comparison sort of 5 elements is a "ranking": a permutation `s` of `Fin 5`
assigning to each position `i` its rank `s i`.  A comparison of positions `i` and `j` returns
`decide (s i < s j)`. -/
abbrev Rank := Equiv.Perm (Fin 5)

/-- A comparison-based decision tree for sorting 5 elements: an internal node compares two
positions and branches on the outcome, a leaf outputs a permutation (the claimed ranking). -/
inductive DTree : Type
  | leaf : Rank → DTree
  | node : Fin 5 → Fin 5 → DTree → DTree → DTree

/-- The worst-case number of comparisons performed by the tree. -/

lemma run_full (s : Rank) : ∀ (L : List (Fin 5 × Fin 5)) (f : List Bool → Rank),
    (full L f).run s = f (ans L s) := by
  intro L
  induction L with
  | nil => intro f; simp [full, DTree.run, ans]
  | cons p L ih =>
      intro f
      by_cases h : s p.1 < s p.2 <;> simp [full, DTree.run, ans, h, ih]

/-- Knowing the outcome of every comparison determines the input ranking. -/
