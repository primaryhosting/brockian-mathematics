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

theorem sorting_lb_5_seven (t : DTree) (hcorrect : ∀ s : Rank, t.run s = s) : 7 ≤ t.depth := by
  have h := sorting_lb_5 t hcorrect
  have hclog : Nat.clog 2 (Nat.factorial 5) = 7 := by norm_num [Nat.factorial]
  rwa [hclog] at h

/-! ## Non-vacuity: a correct comparison-sorting decision tree exists -/

/-- All 25 ordered pairs of positions. -/
