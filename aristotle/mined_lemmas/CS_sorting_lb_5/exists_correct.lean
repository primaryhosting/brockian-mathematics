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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- A comparison-sorting algorithm on `5` elements, modelled as a (binary) decision tree.
A `leaf p` outputs the permutation `p`; a `node i j l r` compares the keys at positions `i`
and `j` and continues in `l` if `key i ≤ key j`, and in `r` otherwise.  This is the standard
decision-tree model: the algorithm's only access to the input is through comparisons. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 5) → DTree
  | node : Fin 5 → Fin 5 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the algorithm, i.e. the depth of the
decision tree. -/

theorem exists_correct : ∃ t : DTree, Correct t := by
  refine ⟨build (Finset.univ : Finset (Fin 5 × Fin 5)).toList Finset.univ, fun τ => ?_⟩
  rw [run_build]
  have hset : (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin 5) => ∀ p ∈ (Finset.univ : Finset (Fin 5 × Fin 5)).toList,
        (σ p.1 ≤ σ p.2 ↔ τ p.1 ≤ τ p.2))) = {τ} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Finset.mem_toList]
    constructor
    · intro hσ
      exact perm_eq_of_agree (fun a b => hσ (a, b) trivial)
    · rintro rfl
      intro p _
      rfl
  rw [hset, pick_singleton]

end CS

