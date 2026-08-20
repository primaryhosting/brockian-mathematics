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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; harmless
since `n * 2 ^ n ≥ 1` for `n ≥ 1`). -/

theorem woodallPrimeInfinitude_iff_unbounded :
    woodallPrimes.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ (woodall n).Prime := by
  rw [WoodallPrimeInfinitude]
  constructor
  · intro h N
    obtain ⟨n, hn, hgt⟩ := h.exists_gt N
    exact ⟨n, hgt, hn.2⟩
  · intro h
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨n, hgt, hp⟩ := h N
    exact absurd (hN ⟨by omega, hp⟩) (by omega)

end Brockian.CullenWoodall

