/-!
# Sylow Exists
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.sylow_exists
Statement: Sylow's first theorem: for a finite group G and a prime p, a Sylow p-subgroup exists — i.e. the type Sylow p G is nonempty. State: for [Group G] [Fintype G] and a prime p, Nonempty (Sylow p G). (Use Mathlib's Sylow existence instance / Sylow.nonempty.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GroupTheory

/-- **Sylow's first theorem**: for a finite group `G` and a prime `p`, a Sylow
`p`-subgroup of `G` exists, i.e. the type `Sylow p G` is nonempty.

The primality hypothesis `hp` is kept as requested; Mathlib's construction of a maximal
`p`-subgroup in fact does not require it. -/
theorem sylow_exists (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime) :
    Nonempty (Sylow p G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact Sylow.nonempty

end GroupTheory


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

