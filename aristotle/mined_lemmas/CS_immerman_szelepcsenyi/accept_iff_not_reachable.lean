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

theorem accept_iff_not_reachable (hs : s < N) {t : ℕ} (ht : t < N) :
    Relation.ReflTransGen (Step N adj s t) start .acc ↔
      ¬ Relation.ReflTransGen (Edge N adj) s t :=
  ⟨not_reachable_of_accept hs, accept_of_not_reachable hs ht⟩

/-! ### The space bound

The complement machine has at most `5 * (N+2)^8` reachable configurations: it uses only
`O(log N)` bits of memory beyond the digraph itself.  Since a nondeterministic machine running
in space `S` on a fixed input has `2^{O(S)}` configurations, this says exactly that the
complement machine also runs in space `O(S)`.
-/

