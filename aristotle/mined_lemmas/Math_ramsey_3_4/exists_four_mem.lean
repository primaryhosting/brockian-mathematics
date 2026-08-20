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

theorem exists_four_mem {V : Type} [DecidableEq V] {s : Finset V} (hs : 4 ≤ s.card) :
    ∃ a b c d : V, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hs
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp ht
  exact ⟨a, b, c, d, hts (by simp), hts (by simp), hts (by simp), hts (by simp),
    hab, hac, had, hbc, hbd, hcd⟩

/-! ### The key combinatorial lemmas -/

/-- `R(3,3) ≤ 6`, in the form: in a triangle-free graph, any set of at least six vertices
contains three pairwise non-adjacent vertices. -/
