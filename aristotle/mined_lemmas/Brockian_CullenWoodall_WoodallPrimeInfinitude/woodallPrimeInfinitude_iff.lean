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

import Mathlib

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; note `W 0 = 0`). -/

theorem woodallPrimeInfinitude_iff :
    WoodallPrimeInfinitude ↔ ∀ N : ℕ, ∃ n, N < n ∧ (woodall n).Prime := by
  constructor
  · intro hinf N
    obtain ⟨p, hp, hlt⟩ := hinf.exists_gt (woodall N)
    obtain ⟨hprime, n, hn, hpn⟩ := hp
    refine ⟨n, ?_, hpn ▸ hprime⟩
    by_contra hle
    push_neg at hle
    have := woodall_monotone hle
    omega
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨n, hn, hp⟩ := h (a + 1)
    have hpos : 0 < n := by omega
    refine ⟨woodall n, ⟨hp, n, hpos, rfl⟩, ?_⟩
    have := le_woodall hpos
    omega

/-- Equivalent form: there are infinitely many Woodall primes iff the set of indices giving
Woodall primes is infinite. -/
