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

theorem filter_lt_succ_of_not_mem {X : Finset ℕ} {v : ℕ} (hv : v ∉ X) :
    (X.filter (fun x => x < v + 1)).card = (X.filter (fun x => x < v)).card := by
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hlt⟩
    refine ⟨hx, ?_⟩
    rcases Nat.lt_or_ge x v with h' | h'
    · exact h'
    · exact absurd (by omega : x = v) (fun h => hv (h ▸ hx))
  · rintro ⟨hx, hlt⟩; exact ⟨hx, by omega⟩

