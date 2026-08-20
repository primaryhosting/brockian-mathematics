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

theorem hasRamseyProp34_nine : HasRamseyProp34 9 := by
  intro G
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  refine no_good_graph_nine G ?_ ?_
  · intro a b c hab hac hbc
    obtain ⟨s, hcard, hcl⟩ := clique_three_of_adj G a b c hab.ne hac.ne hbc.ne hab hac hbc
    exact h1 s hcard hcl
  · intro a b c d hab hac had hbc hbd hcd n1 n2 n3 n4 n5 n6
    obtain ⟨t, hcard, hin⟩ :=
      indep_four_of_not_adj G a b c d hab hac had hbc hbd hcd n1 n2 n3 n4 n5 n6
    exact h2 t hcard hin

/-- **The Ramsey number `R(3,4)` equals `9`**: nine is the least `n` such that every graph
on `n` vertices contains a triangle or an independent set of size four. -/
