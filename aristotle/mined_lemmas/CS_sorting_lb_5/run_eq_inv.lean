/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-- A comparison-based decision tree sorting 5 elements: an internal node
`node i j l r` compares the keys at positions `i` and `j`, descending into `l`
when `a i ≤ a j` and into `r` otherwise; a leaf outputs a permutation of the
positions. -/
inductive CompTree where
  | leaf : Equiv.Perm (Fin 5) → CompTree
  | node : Fin 5 → Fin 5 → CompTree → CompTree → CompTree
  deriving Inhabited

namespace CompTree

/-- The worst-case number of comparisons performed by the decision tree. -/

lemma run_eq_inv (t : CompTree) (h : Sorts t) (p : Equiv.Perm (Fin 5)) :
    run (fun i => ((p i : Fin 5) : ℕ)) t = p⁻¹ := by
  have hainj : Function.Injective (fun i => ((p i : Fin 5) : ℕ)) := by
    intro x y hxy
    exact p.injective (Fin.val_injective hxy)
  have hmono := h _ hainj
  obtain ⟨σ, hσ⟩ : ∃ σ, run (fun i => ((p i : Fin 5) : ℕ)) t = σ := ⟨_, rfl⟩
  rw [hσ] at hmono ⊢
  have hmono' : Monotone ⇑(p * σ) := by
    intro x y hxy
    have hxy' := hmono hxy
    simp only [Function.comp_apply] at hxy'
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Fin.le_def]
    exact hxy'
  have hpσ : p * σ = 1 := (Equiv.Perm.monotone_iff _).mp hmono'
  exact (inv_eq_of_mul_eq_one_right hpσ).symm

end CompTree

/-- **Comparison-sort lower bound for 5 elements.** Any correct comparison-based
sorting decision tree on 5 elements has worst-case depth (number of
comparisons) at least `⌈log₂(5!)⌉ = 7`. -/
