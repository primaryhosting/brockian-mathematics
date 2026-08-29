/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace Math2

/-- The affine plane curve `C(m,n) = {(x,y) | y ^ n = x ^ m}`. -/

lemma eq_one_of_coprime_pow {k : Type*} [Field k] {m n : ℕ} (h : Nat.Coprime m n) {u : k}
    (hu : u ≠ 0) (hm : u ^ m = 1) (hn : u ^ n = 1) : u = 1 := by
  have hgcd : (1 : ℤ) = (m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n := by
    have hab := Nat.gcd_eq_gcd_ab m n
    rw [Nat.Coprime.gcd_eq_one h] at hab
    exact_mod_cast hab
  calc u = u ^ (1 : ℤ) := (zpow_one u).symm
    _ = u ^ ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n) := by rw [← hgcd]
    _ = (u ^ (m : ℤ)) ^ (Nat.gcdA m n) * (u ^ (n : ℤ)) ^ (Nat.gcdB m n) := by
        rw [zpow_add₀ hu, ← zpow_mul, ← zpow_mul]
    _ = 1 := by rw [zpow_natCast, zpow_natCast, hm, hn, one_zpow, one_zpow, one_mul]

