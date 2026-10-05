/-
# Sylow Exists
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.sylow_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sylow Exists
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.sylow_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace GroupTheory

/-- **Sylow's first theorem.** For a finite group `G` and a prime `p`, a Sylow
`p`-subgroup of `G` exists, i.e. the type `Sylow p G` is nonempty.

The primality hypothesis `hp` (and finiteness of `G`) are kept because they were part of the
requested statement, but they are in fact not needed: `Sylow p G` is the type of maximal
`p`-subgroups, and it is nonempty for every natural number `p` and every group `G`. -/
theorem sylow_exists (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime) :
    Nonempty (Sylow p G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact Sylow.nonempty

end GroupTheory

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

