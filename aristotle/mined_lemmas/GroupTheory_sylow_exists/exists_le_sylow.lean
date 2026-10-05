import Mathlib

/-!
# Sylow Exists
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.sylow_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace GroupTheory

/-- **Sylow's first theorem**: for a finite group `G` and a prime `p`, a Sylow `p`-subgroup
of `G` exists, i.e. the type `Sylow p G` is nonempty.

The primality hypothesis `hp` is kept because it is part of the requested statement; it is in
fact not needed, since `Sylow p G` is nonempty for every natural number `p` (the trivial
subgroup is a `p`-group, and every `p`-subgroup of a finite group is contained in a maximal
one). -/

theorem exists_le_sylow (G : Type*) [Group G] [Fintype G] (p : ℕ)
    (P : Subgroup G) (hP : IsPGroup p P) : ∃ Q : Sylow p G, P ≤ Q :=
  hP.exists_le_sylow

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

