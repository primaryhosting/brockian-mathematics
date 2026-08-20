/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: verified (axiom-clean: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree sorting 4 elements.  A `leaf` outputs a
permutation (the claimed sorted order / ranking of the input), and a `node i j`
compares the input keys at positions `i` and `j` and branches accordingly. -/
inductive DTree where
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the tree. -/

theorem perm_eq_of_lt_iff {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (h : ∀ i j, σ i < σ j ↔ τ i < τ j) : σ = τ := by
  have key : ∀ a b : Equiv.Perm (Fin n), (∀ i j, a i < a j ↔ b i < b j) →
      ∀ x, x ≤ b (a.symm x) := by
    intro a b hab
    have hmono : StrictMono (a.symm.trans b) := by
      intro x y hxy
      have hx : a (a.symm x) < a (a.symm y) := by simpa using hxy
      simpa using (hab (a.symm x) (a.symm y)).1 hx
    intro x
    simpa using hmono.le_apply (x := x)
  have h1 := key σ τ h
  have h2 := key τ σ fun i j => (h i j).symm
  refine Equiv.ext fun x => ?_
  have a1 : σ x ≤ τ x := by simpa using h1 (σ x)
  have a2 : τ x ≤ σ x := by simpa using h2 (τ x)
  exact le_antisymm a1 a2

/-- All pairs of indices. -/
