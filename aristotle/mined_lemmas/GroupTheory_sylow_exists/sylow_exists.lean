/-
# Sylow Exists
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.sylow_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GroupTheory

open scoped Pointwise

/-- Key intermediate lemma: for a finite group `G` and a prime `p`, there is a subgroup of `G`
whose cardinality is `p ^ n`, where `p ^ n` is the largest power of `p` dividing `|G|`.
This is the substantive content of Sylow's first theorem. -/

theorem sylow_exists (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime) :
    Nonempty (Sylow p G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, hH⟩ := exists_subgroup_card_eq_pow_factorization G p hp
  exact ⟨Sylow.ofCard H hH⟩

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

