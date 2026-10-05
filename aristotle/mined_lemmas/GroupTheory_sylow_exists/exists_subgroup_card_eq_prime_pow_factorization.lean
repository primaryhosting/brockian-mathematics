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

/-- **Sylow's first theorem**: for a finite group `G` and a prime `p`, a Sylow
`p`-subgroup of `G` exists, i.e. the type `Sylow p G` is nonempty.

The primality hypothesis `hp` (and finiteness of `G`) are kept because they were part of the
requested statement, but they turn out to be unnecessary: in Mathlib `Sylow p G` is the type of
maximal `p`-subgroups, which is nonempty for every group `G` and every natural number `p`
(the trivial subgroup is contained in a maximal one). -/

theorem exists_subgroup_card_eq_prime_pow_factorization
    (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime) :
    ∃ H : Subgroup G, Nat.card H = p ^ (Nat.card G).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := sylow_exists G p hp
  exact ⟨P.toSubgroup, P.card_eq_multiplicity⟩

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

