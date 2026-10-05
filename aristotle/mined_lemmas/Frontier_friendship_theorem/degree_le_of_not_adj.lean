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

import Mathlib

/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph satisfies the *friendship condition* when any two distinct vertices have
exactly one common neighbour ("every two people have exactly one common friend"). -/

lemma degree_le_of_not_adj (hG : Friendship G) {v w : V} (hvw : v ≠ w) (h : ¬ G.Adj v w) :
    G.degree v ≤ G.degree w := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have key : ∀ x : V, x ≠ w → ∃ u, G.Adj x u ∧ G.Adj w u := fun x hx => (hG hx).exists
  set F : V → V := fun x => if hx : x = w then x else (key x hx).choose with hF
  have hFspec : ∀ x : V, x ≠ w → G.Adj x (F x) ∧ G.Adj w (F x) := by
    intro x hx
    simp only [hF, dif_neg hx]
    exact (key x hx).choose_spec
  apply Finset.card_le_card_of_injOn F
  · intro x hx
    simp only [Finset.mem_coe, mem_neighborFinset] at hx ⊢
    have hxw : x ≠ w := by rintro rfl; exact h hx
    exact (hFspec x hxw).2
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_neighborFinset] at hx hy
    have hxw : x ≠ w := by rintro rfl; exact h hx
    have hyw : y ≠ w := by rintro rfl; exact h hy
    by_contra hne
    have h1 : G.Adj x (F x) ∧ G.Adj y (F x) :=
      ⟨(hFspec x hxw).1, by rw [hxy]; exact (hFspec y hyw).1⟩
    have h2 : G.Adj x v ∧ G.Adj y v := ⟨hx.symm, hy.symm⟩
    have hvF := (hG hne).unique h1 h2
    rw [← hvF] at h
    exact h ((hFspec x hxw).2).symm

/-- Two distinct non-adjacent vertices of a friendship graph have the same degree. -/
