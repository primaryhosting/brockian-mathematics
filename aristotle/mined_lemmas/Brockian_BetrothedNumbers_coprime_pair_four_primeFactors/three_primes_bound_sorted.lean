import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

lemma three_primes_bound_sorted {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) :
    p * q * r ≤ 4 * ((p - 1) * ((q - 1) * (r - 1))) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq3 : 3 ≤ q := by omega
  have hr5 : 5 ≤ r := by
    have hr4 : 4 ≤ r := by omega
    rcases eq_or_lt_of_le hr4 with h | h
    · exact absurd (h ▸ hr) (by norm_num)
    · omega
  obtain ⟨P, rfl⟩ : ∃ P, p = P + 1 := ⟨p - 1, by omega⟩
  obtain ⟨Q, rfl⟩ : ∃ Q, q = Q + 1 := ⟨q - 1, by omega⟩
  obtain ⟨R, rfl⟩ : ∃ R, r = R + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hP : 1 ≤ P := by omega
  have hQ : 2 ≤ Q := by omega
  have hR : 4 ≤ R := by omega
  have e1 : 4 * (P * Q) ≤ P * Q * R := by
    calc 4 * (P * Q) = P * Q * 4 := by ring
      _ ≤ P * Q * R := Nat.mul_le_mul_left _ hR
  have e2 : 2 * (P * R) ≤ P * Q * R := by
    calc 2 * (P * R) = P * 2 * R := by ring
      _ ≤ P * Q * R := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hQ)
  have e3 : Q * R ≤ P * Q * R := by
    calc Q * R = 1 * Q * R := by ring
      _ ≤ P * Q * R := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hP)
  have e4 : 8 * P ≤ P * Q * R := by
    calc 8 * P = P * (2 * 4) := by ring
      _ ≤ P * (Q * R) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hQ hR)
      _ = P * Q * R := by ring
  have e5 : 4 * Q ≤ P * Q * R := by
    calc 4 * Q = 1 * Q * 4 := by ring
      _ ≤ P * Q * R := Nat.mul_le_mul (Nat.mul_le_mul_right _ hP) hR
  have e6 : 2 * R ≤ P * Q * R := by
    calc 2 * R = 1 * 2 * R := by ring
      _ ≤ P * Q * R := Nat.mul_le_mul_right _ (Nat.mul_le_mul hP hQ)
  have e7 : 8 ≤ P * Q * R := by
    calc (8 : ℕ) = 1 * 2 * 4 := by norm_num
      _ ≤ P * Q * R := Nat.mul_le_mul (Nat.mul_le_mul hP hQ) hR
  nlinarith [e1, e2, e3, e4, e5, e6, e7]

/-- Three distinct primes: `p q r ≤ 4 (p-1)(q-1)(r-1)`. -/
