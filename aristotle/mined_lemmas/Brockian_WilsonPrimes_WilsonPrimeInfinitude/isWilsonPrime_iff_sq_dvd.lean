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

theorem isWilsonPrime_iff_sq_dvd {n : ℕ} (hn : n ≠ 1) :
    IsWilsonPrime n ↔ n ^ 2 ∣ (n - 1)! + 1 := by
  refine ⟨fun h => h.2, fun hd => ⟨?_, hd⟩⟩
  have hdvd : n ∣ (n - 1)! + 1 := dvd_trans (dvd_pow_self n two_ne_zero) hd
  have h0 : (((n - 1)! + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have h : (((n - 1)! : ℕ) : ZMod n) = -1 := by
    push_cast at h0 ⊢
    linear_combination h0
  exact Nat.prime_of_fac_equiv_neg_one h hn

/-- `2` is not a Wilson prime. -/
