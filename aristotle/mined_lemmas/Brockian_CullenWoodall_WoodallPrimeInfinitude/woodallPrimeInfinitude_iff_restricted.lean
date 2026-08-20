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

theorem woodallPrimeInfinitude_iff_restricted :
    WoodallPrimeInfinitude ↔
      ∀ N : ℕ, ∃ n, N < n ∧ (n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3) ∧
        (woodall n).Prime := by
  rw [woodallPrimeInfinitude_iff]
  constructor
  · intro h N
    obtain ⟨n, hn, hp⟩ := h N
    have hnc : ¬ (n % 6 = 4 ∨ n % 6 = 5) := fun hc => not_prime_woodall_of_mod_six hc hp
    exact ⟨n, hn, by omega, hp⟩
  · intro h N
    obtain ⟨n, hn, _, hp⟩ := h N
    exact ⟨n, hn, hp⟩

end Brockian.CullenWoodall

