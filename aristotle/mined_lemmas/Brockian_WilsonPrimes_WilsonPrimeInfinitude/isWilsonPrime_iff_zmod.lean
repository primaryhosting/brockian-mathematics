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
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2 ∣ (p - 1)! + 1`
(equivalently, Wilson's congruence `(p-1)! ≡ -1` holds modulo `p ^ 2`). -/

theorem isWilsonPrime_iff_zmod {p : ℕ} (hp : p.Prime) :
    IsWilsonPrime p ↔ (((p - 1)! : ℕ) : ZMod (p ^ 2)) = -1 := by
  constructor
  · rintro ⟨-, hd⟩
    have h : (((p - 1)! + 1 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at h
    linear_combination h
  · intro h
    refine ⟨hp, ?_⟩
    refine (ZMod.natCast_eq_zero_iff _ _).mp ?_
    push_cast
    rw [h]
    ring

/-- The primality requirement in `IsWilsonPrime` is automatic: for `n ≠ 1`, the congruence
`n ^ 2 ∣ (n - 1)! + 1` already forces `n` to be prime (converse of Wilson's theorem). -/
