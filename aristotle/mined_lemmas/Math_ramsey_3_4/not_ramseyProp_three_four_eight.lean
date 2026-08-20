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

namespace Math

/-- `RamseyProp s t n` says that for every graph `G` on `n` vertices (equivalently, every
two-colouring of the edges of the complete graph on `n` vertices) either `G` contains a clique
of size `s`, or the complement of `G` contains a clique of size `t` (i.e. `G` contains an
independent set of size `t`). -/

theorem not_ramseyProp_three_four_eight : ¬ RamseyProp 3 4 8 := by
  intro h
  rcases h wagner with h | h
  · exact h wagner_cliqueFree_three
  · exact h wagner_compl_cliqueFree_four

/-- **The Ramsey number `R(3,4)` equals `9`.** -/
