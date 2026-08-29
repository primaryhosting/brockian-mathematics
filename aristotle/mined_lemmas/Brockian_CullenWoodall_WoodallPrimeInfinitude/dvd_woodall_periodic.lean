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

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/

theorem dvd_woodall_periodic {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) :
    (p ∣ woodall n ↔ p ∣ woodall (n + p * (p - 1))) := by
  have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hodd)
  have hferm : (2:ℕ) ^ (p - 1) ≡ 1 [MOD p] := by
    have := Nat.ModEq.pow_totient h2
    rwa [Nat.totient_prime hp] at this
  have hpow : (2:ℕ) ^ (n + p * (p - 1)) ≡ 2 ^ n [MOD p] := by
    calc (2:ℕ) ^ (n + p * (p - 1)) = 2 ^ n * ((2 ^ (p - 1)) ^ p) := by
          rw [pow_add, ← pow_mul, mul_comm p (p - 1)]
      _ ≡ 2 ^ n * 1 ^ p [MOD p] := Nat.ModEq.mul_left _ (hferm.pow p)
      _ = 2 ^ n := by ring
  have hidx : (n + p * (p - 1)) ≡ n [MOD p] := by
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]
  have hmul : (n + p * (p - 1)) * 2 ^ (n + p * (p - 1)) ≡ n * 2 ^ n [MOD p] := hidx.mul hpow
  rw [dvd_woodall_iff hn, dvd_woodall_iff (by omega : 1 ≤ n + p * (p - 1))]
  exact ⟨fun h => hmul.trans h, fun h => hmul.symm.trans h⟩

/-- For every odd prime `p` there is an index `n ≥ 1` with `p ∣ W n`.

The witness is obtained from the Chinese remainder theorem: any `n` with
`n ≡ 1 (mod p-1)` and `n ≡ (p+1)/2 (mod p)` satisfies `n * 2 ^ n ≡ 1 (mod p)`. -/
