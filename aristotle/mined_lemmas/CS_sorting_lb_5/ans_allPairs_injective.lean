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

lemma ans_allPairs_injective : Function.Injective (ans allPairs) := by
  intro s t hst
  have key : ∀ i j : Fin 5, s i < s j ↔ t i < t j := by
    intro i j
    have h := (List.map_inj_left.1 hst) (i, j) (mem_allPairs i j)
    simpa using h
  set e : Rank := t.symm.trans s with he_def
  have he : StrictMono (e : Fin 5 → Fin 5) := by
    intro a b hab
    have : t (t.symm a) < t (t.symm b) := by simpa using hab
    simpa [he_def] using (key (t.symm a) (t.symm b)).2 this
  have hesymm : StrictMono (e.symm : Fin 5 → Fin 5) := by
    intro a b hab
    by_contra hcon
    push_neg at hcon
    have := he.monotone hcon
    simp only [Equiv.apply_symm_apply] at this
    exact absurd hab (not_lt.2 this)
  have hfix : ∀ x : Fin 5, e x = x := by
    intro x
    have h1 : x ≤ e x := he.le_apply
    have h2 : x ≤ e.symm x := hesymm.le_apply
    have h3 : e x ≤ x := by
      have := he.monotone h2
      simpa using this
    exact le_antisymm h3 h1
  refine Equiv.ext fun y => ?_
  simpa [he_def] using hfix (t y)

open Classical in
/-- A leaf labelling: given the answers to all comparisons, output a ranking consistent
with them. -/
