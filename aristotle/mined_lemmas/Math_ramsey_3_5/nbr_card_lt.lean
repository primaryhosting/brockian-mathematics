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

theorem nbr_card_lt {k : ℕ} {s : Finset V} {v : V} (hv : v ∈ s) (h3 : NoCliqueIn G 3 s)
    (hk : NoCliqueIn Gᶜ k s) : (s ∩ G.neighborFinset v).card < k :=
  card_lt_of_isClique (nbrs_indep hv h3) hk Finset.inter_subset_left

/-- The non-neighbours of `v` inside `s` contain no `k`-independent set, if `s` contains no
`(k+1)`-independent set. -/
