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

theorem indep_four_of_not_adj {V : Type} [DecidableEq V] (G : SimpleGraph V) (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : ¬ G.Adj a b) (h2 : ¬ G.Adj a c) (h3 : ¬ G.Adj a d)
    (h4 : ¬ G.Adj b c) (h5 : ¬ G.Adj b d) (h6 : ¬ G.Adj c d) :
    ∃ t : Finset V, t.card = 4 ∧ G.IsIndepSet (↑t : Set V) := by
  refine ⟨{a, b, c, d}, by
    rw [Finset.card_eq_four]; exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩, ?_⟩
  simp only [Finset.coe_insert, Finset.coe_singleton]
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hxy
      | assumption
      | exact fun h => h1 h.symm
      | exact fun h => h2 h.symm
      | exact fun h => h3 h.symm
      | exact fun h => h4 h.symm
      | exact fun h => h5 h.symm
      | exact fun h => h6 h.symm

/-- Extract three distinct elements from a finset of cardinality at least three. -/
