import Mathlib

/-!
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- A *comparison sorting algorithm* on `n` real-valued keys, modelled as a decision tree.
Each internal node `node i j l r` compares the keys at positions `i` and `j` of the input and
branches to `l` if `a i ≤ a j`, to `r` otherwise; each leaf outputs a permutation of the
positions (the claimed sorting order).  Only comparisons of input keys are allowed. -/
inductive CompTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n

namespace CompTree

variable {n : ℕ}

/-- The permutation output by the algorithm on the input `a`. -/

theorem exists_correct_comparison_sort_two :
    ∃ t : CompTree 2, (∀ a : Fin 2 → ℝ, Function.Injective a → StrictMono (a ∘ t.run a)) ∧
      t.depth = 1 := by
  refine ⟨CompTree.node 0 1 (CompTree.leaf 1) (CompTree.leaf (Equiv.swap 0 1)), ?_, rfl⟩
  intro a ha
  have hne : a 0 ≠ a 1 := fun h => by simpa using ha h
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  by_cases h : a 0 ≤ a 1
  · simp only [CompTree.run, h, if_true, Function.comp_apply]
    simp only [Equiv.Perm.coe_one, id_eq]
    exact lt_of_le_of_ne h hne
  · simp only [CompTree.run, h, if_false, Function.comp_apply]
    push_neg at h
    simpa [Equiv.swap_apply_def] using h

/-- Restatement of the lower bound with the explicit constant `7`. -/
