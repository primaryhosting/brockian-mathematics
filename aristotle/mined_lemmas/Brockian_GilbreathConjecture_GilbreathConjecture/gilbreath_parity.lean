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
# The Gilbreath triangle: definition and explicit values

Auxiliary file for `Brockian.GilbreathConjecture`.  It sets up the Gilbreath triangle of the
primes and records the explicit values of its first eleven rows (as far as they are
determined by the first `45` primes).
-/

namespace Brockian.GilbreathConjecture

/-- Row `n`, entry `k` of the Gilbreath triangle of the prime numbers:
row `0` is the sequence of primes, and each later row consists of the absolute values of the
differences of consecutive entries of the previous row. -/

theorem gilbreath_parity (n : ℕ) :
    Odd (gilbreath (n + 1) 0) ∧ ∀ k, 1 ≤ k → Even (gilbreath (n + 1) k) := by
  induction n with
  | zero =>
    refine ⟨by rw [gilbreath_1_00]; decide, ?_⟩
    intro k hk
    have h1 : Odd (Nat.nth Nat.Prime k) := odd_nth_prime hk
    have h2 : Odd (Nat.nth Nat.Prime (k + 1)) := odd_nth_prime (by omega)
    rw [Nat.even_iff, gilbreath_succ, gilbreath_zero, gilbreath_zero, natAbs_sub_mod_two]
    rw [Nat.odd_iff] at h1 h2
    omega
  | succ n ih =>
    obtain ⟨h0, hk⟩ := ih
    rw [Nat.odd_iff] at h0
    have h1 := hk (0 + 1) (by omega)
    rw [Nat.even_iff] at h1
    refine ⟨?_, ?_⟩
    · rw [Nat.odd_iff, gilbreath_succ, natAbs_sub_mod_two]
      omega
    · intro k hkk
      have ha := hk k hkk
      have hb := hk (k + 1) (by omega)
      rw [Nat.even_iff] at ha hb ⊢
      rw [gilbreath_succ, natAbs_sub_mod_two]
      omega

/-- The first entry of any row after row `0` is odd. -/
