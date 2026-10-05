/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based sorting algorithm for 3 elements, modelled as a decision tree.
An internal node `cmp i j yes no` compares the entries at positions `i` and `j` of the
input, and branches to `yes` if `x i ≤ x j` and to `no` otherwise.  A leaf is labelled
by the permutation the algorithm outputs. -/
inductive CTree where
  | leaf : Equiv.Perm (Fin 3) → CTree
  | cmp : Fin 3 → Fin 3 → CTree → CTree → CTree
  deriving Inhabited

namespace CTree

/-- The result of running the decision tree on the input `x`. -/

lemma mem_reachable_of_sorts {t : CTree} (ht : Sorts t) (s : Equiv.Perm (Fin 3)) :
    s ∈ reachable t := by
  have hinj : Function.Injective (fun i : Fin 3 => ((s⁻¹ i : Fin 3) : ℕ)) := by
    intro a b hab
    simp only at hab
    have h1 : (s⁻¹ a : Fin 3) = s⁻¹ b := Fin.val_injective hab
    simpa using congrArg (fun z => s z) h1
  have hmono := ht _ hinj
  have key : s⁻¹ * run t (fun i : Fin 3 => ((s⁻¹ i : Fin 3) : ℕ)) = 1 := by
    refine perm_eq_one_of_monotone _ ?_
    intro a b hab
    have h2 := hmono a b hab
    simp only [Equiv.Perm.mul_apply, Fin.le_def]
    simpa using h2
  rw [inv_mul_eq_one.mp key]
  exact run_mem_reachable t _

end CTree

/-- **Comparison-sorting lower bound for 3 elements.**
Any comparison-based sorting algorithm for 3 elements (modelled as a comparison decision
tree that correctly sorts every input with distinct entries) must perform at least
`⌈log₂ 3!⌉ = 3` comparisons in the worst case. -/
