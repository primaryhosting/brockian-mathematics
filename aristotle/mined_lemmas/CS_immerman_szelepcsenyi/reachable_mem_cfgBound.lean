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

/-
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS
namespace IS

/-!
## The reachability sets of a finite digraph

Throughout, the digraph has vertex set `{0, 1, ..., N-1} ⊆ ℕ` and edge relation `adj`.
`R N adj s i` is the set of vertices reachable from `s` using at most `i` edges.
-/

/-- The edge relation of the digraph on vertex set `{0,...,N-1}`. -/

theorem reachable_mem_cfgBound (hs : s < N) {t : ℕ} (ht : t < N) {x : Cfg}
    (hx : Relation.ReflTransGen (Step N adj s t) start x) : x ∈ cfgBound N :=
  mem_cfgBound_of_Inv hs ht (Inv_of_reachable hs hx)

/-! ### Locality: each transition inspects at most one entry of the adjacency matrix

This shows that the complement machine is a *bona fide* machine: a transition is not allowed
to perform a hidden computation on the input graph, it may consult a single entry of the
adjacency matrix, determined by the two configurations involved. -/

/-- The single adjacency entry (if any) that a transition from `x` to `y` inspects. -/
