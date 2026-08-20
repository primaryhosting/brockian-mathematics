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

theorem woodallPrimeInfinitude_iff_indices_infinite :
    WoodallPrimeInfinitude ↔ {n : ℕ | 0 < n ∧ (woodall n).Prime}.Infinite := by
  rw [woodallPrimeInfinitude_iff]
  constructor
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨n, hn, hp⟩ := h a
    exact ⟨n, ⟨by omega, hp⟩, hn⟩
  · intro hinf N
    obtain ⟨n, hn, hlt⟩ := hinf.exists_gt N
    exact ⟨n, hlt, hn.2⟩

/-- A sharpened reduction: since indices `≡ 4, 5 (mod 6)` always give composite Woodall
numbers, the conjecture is equivalent to the existence of arbitrarily large prime-producing
indices among `n ≡ 0, 1, 2, 3 (mod 6)`. -/
