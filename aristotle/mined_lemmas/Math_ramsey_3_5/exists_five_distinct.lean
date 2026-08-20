import Mathlib
import RequestProject.Ramsey

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
# The Ramsey number `R(3,5) = 14`

This file proves that `14` is the least `n` such that every simple graph on `n` vertices
contains a triangle (a `3`-clique) or an independent set of size `5` (a `5`-clique of the
complement).
-/

namespace Math

open Finset SimpleGraph

section Bounds

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `NoCliqueIn G n s` says that `G` has no `n`-clique contained in the vertex set `s`. -/

theorem exists_five_distinct {α : Type*} [DecidableEq α] {t : Finset α} (h : t.card = 5) :
    ∃ a b c d e : α, a ∈ t ∧ b ∈ t ∧ c ∈ t ∧ d ∈ t ∧ e ∈ t ∧
      b ≠ a ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d := by
  obtain ⟨a, t1, ha, rfl, h1⟩ := Finset.card_eq_succ.1 h
  obtain ⟨b, t2, hb, rfl, h2⟩ := Finset.card_eq_succ.1 h1
  obtain ⟨c, t3, hc, rfl, h3⟩ := Finset.card_eq_succ.1 h2
  obtain ⟨d, t4, hd, rfl, h4⟩ := Finset.card_eq_succ.1 h3
  obtain ⟨e, rfl⟩ := Finset.card_eq_one.1 h4
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb hc hd ⊢
  exact ⟨a, b, c, d, e, by tauto, by tauto, by tauto, by tauto, by tauto,
    fun h => ha.1 h.symm, fun h => ha.2.1 h.symm, fun h => hb.1 h.symm,
    fun h => ha.2.2.1 h.symm, fun h => hb.2.1 h.symm, fun h => hc.1 h.symm,
    fun h => ha.2.2.2 h.symm, fun h => hb.2.2 h.symm, fun h => hc.2 h.symm, fun h => hd h.symm⟩

/-- `graph13` is triangle-free. -/
