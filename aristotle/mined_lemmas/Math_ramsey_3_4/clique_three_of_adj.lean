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

set_option maxRecDepth 10000
set_option synthInstance.maxSize 400
set_option synthInstance.maxHeartbeats 1000000

namespace Math

open Finset SimpleGraph

/-- `HasRamseyProp34 n` holds when every simple graph on `n` vertices contains either a
clique of size `3` or an independent set of size `4`; equivalently, every red/blue colouring
of the edges of `K n` contains a red triangle or a blue `K 4`. -/

theorem clique_three_of_adj {V : Type} [DecidableEq V] (G : SimpleGraph V) (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : G.Adj a b) (h2 : G.Adj a c) (h3 : G.Adj b c) :
    ∃ s : Finset V, s.card = 3 ∧ G.IsClique (↑s : Set V) := by
  refine ⟨{a, b, c}, by rw [Finset.card_eq_three]; exact ⟨a, b, c, hab, hac, hbc, rfl⟩, ?_⟩
  simp only [Finset.coe_insert, Finset.coe_singleton]
  rw [SimpleGraph.isClique_iff]
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hxy
      | assumption
      | exact h1.symm
      | exact h2.symm
      | exact h3.symm

