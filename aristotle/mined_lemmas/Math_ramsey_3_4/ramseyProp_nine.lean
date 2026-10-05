/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset SimpleGraph

/-! ## A decidable reformulation of `CliqueFree` -/

/-- `G.CliqueFree n` says: no finset of `n` pairwise-adjacent vertices. -/

theorem ramseyProp_nine : RamseyProp 9 3 4 := by
  intro G
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  classical
  have hcard : Fintype.card (Fin 9) = 9 := by simp
  have hdeg : ∀ v : Fin 9, G.degree v = 3 := fun v =>
    le_antisymm (degree_le_three G h3 h4 v) (three_le_degree G hcard h3 h4 v)
  have hsum : ∑ v : Fin 9, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul] at hsum
  omega

/-! ## The main theorem -/

/-- **The Ramsey number `R(3,4)` equals 9**: 9 is the least `n` such that every graph on `n`
vertices contains a triangle or an independent set of size 4, and there is a graph on 8
vertices with neither. -/
