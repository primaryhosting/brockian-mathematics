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

theorem perm_eq_of_le_iff (σ τ : Equiv.Perm (Fin 4))
    (h : ∀ i j : Fin 4, σ i ≤ σ j ↔ τ i ≤ τ j) : σ = τ := by
  have hf : ∀ a b : Fin 4, a ≤ b ↔ (τ (σ.symm a)) ≤ (τ (σ.symm b)) := by
    intro a b
    have := h (σ.symm a) (σ.symm b)
    simpa using this
  let f : Fin 4 ≃o Fin 4 := ⟨σ.symm.trans τ, by intro a b; simpa using (hf a b).symm⟩
  have hid : f = OrderIso.refl _ := Subsingleton.elim _ _
  have h2 : ∀ a, τ (σ.symm a) = a := by
    intro a
    have := congrArg (fun g => g a) hid
    simpa [f] using this
  ext i
  have h3 := h2 (σ i)
  simp only [Equiv.symm_apply_apply] at h3
  simp [h3]

/-- Build a decision tree which asks the comparisons in `pairs` in order and, at each leaf,
outputs the first candidate consistent with the answers received. -/
