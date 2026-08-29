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

theorem build_correct :
    ∀ (pairs : List (Fin 4 × Fin 4)) (cands : List (Equiv.Perm (Fin 4)))
      (σ : Equiv.Perm (Fin 4)), σ ∈ cands →
      (∀ τ ∈ cands, (∀ p ∈ pairs, (σ p.1 ≤ σ p.2 ↔ τ p.1 ≤ τ p.2)) → τ = σ) →
      run (build pairs cands) σ = σ
  | [], cands, σ, hmem, huniq => by
      have hne : cands ≠ [] := by
        intro hnil
        rw [hnil] at hmem
        simp at hmem
      have hhead : cands.headI ∈ cands := by
        cases cands with
        | nil => exact absurd rfl hne
        | cons a l => simp
      simpa [run, build] using huniq _ hhead (by simp)
  | (i, j) :: rest, cands, σ, hmem, huniq => by
      by_cases hc : σ i ≤ σ j
      · have hmem' : σ ∈ cands.filter (fun σ => decide (σ i ≤ σ j)) := by
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hmem, hc⟩
        have huniq' : ∀ τ ∈ cands.filter (fun σ => decide (σ i ≤ σ j)),
            (∀ p ∈ rest, (σ p.1 ≤ σ p.2 ↔ τ p.1 ≤ τ p.2)) → τ = σ := by
          intro τ hτ hagree
          simp only [List.mem_filter, decide_eq_true_eq] at hτ
          refine huniq τ hτ.1 ?_
          intro p hp
          rcases List.mem_cons.mp hp with hp | hp
          · subst hp; simp [hc, hτ.2]
          · exact hagree p hp
        simp only [run, build, if_pos hc]
        exact build_correct rest _ σ hmem' huniq'
      · have hmem' : σ ∈ cands.filter (fun σ => decide ¬ (σ i ≤ σ j)) := by
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hmem, hc⟩
        have huniq' : ∀ τ ∈ cands.filter (fun σ => decide ¬ (σ i ≤ σ j)),
            (∀ p ∈ rest, (σ p.1 ≤ σ p.2 ↔ τ p.1 ≤ τ p.2)) → τ = σ := by
          intro τ hτ hagree
          simp only [List.mem_filter, decide_eq_true_eq] at hτ
          refine huniq τ hτ.1 ?_
          intro p hp
          rcases List.mem_cons.mp hp with hp | hp
          · subst hp; simp [hc, hτ.2]
          · exact hagree p hp
        simp only [run, build, if_neg hc]
        exact build_correct rest _ σ hmem' huniq'

/-- The list of all ordered pairs of indices. -/
