import Mathlib
/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
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

set_option grind.warning false

namespace CS

/-- A comparison-based decision tree sorting 4 elements.

An input is modelled by a permutation `σ : Equiv.Perm (Fin 4)`, where `σ i` is the rank
of the `i`-th input element (so all inputs are distinct and every ranking occurs).
An internal node `node i j l r` performs the single comparison `σ i ≤ σ j`, i.e. it asks
whether the `i`-th element is smaller than the `j`-th element, and branches accordingly.
A leaf outputs a permutation, the algorithm's claimed ranking of the input. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree

/-- The output of the decision tree on the input with ranking `σ`. -/

theorem factorial_le_two_pow_depth (t : DTree) (h : Correct t) :
    Nat.factorial 4 ≤ 2 ^ depth t := by
  have himg : Finset.univ.image (run t) = (Finset.univ : Finset (Equiv.Perm (Fin 4))) := by
    apply Finset.eq_univ_of_forall
    intro σ
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨σ, h σ⟩
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card = Nat.factorial 4 := by
    simp [Fintype.card_perm]
  have := card_outputs_le t
  rw [himg, hcard] at this
  exact this

/-- Any correct comparison sort of 4 elements performs at least 5 comparisons
in the worst case. -/
