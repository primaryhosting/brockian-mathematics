import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
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

namespace Frontier

open Filter

/-- `primeGap n = p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n` is the `n`-th prime
(with `p_0 = 2`). -/

theorem exists_primeGap_gt (B : ℕ) : ∃ n, B < primeGap n := by
  simp only [primeGap]
  have hMpos : 0 < (B + 2)! := Nat.factorial_pos _
  have hMge : B + 2 ≤ (B + 2)! := Nat.self_le_factorial _
  have hnp : ∀ q, (B + 2)! + 2 ≤ q → q ≤ (B + 2)! + B + 2 → ¬ q.Prime := by
    intro q h1 h2 hq
    have hdvdM : (q - (B + 2)!) ∣ (B + 2)! := Nat.dvd_factorial (by omega) (by omega)
    have hsum : (q - (B + 2)!) ∣ ((B + 2)! + (q - (B + 2)!)) := Dvd.dvd.add hdvdM dvd_rfl
    rw [show (B + 2)! + (q - (B + 2)!) = q from by omega] at hsum
    rcases hq.eq_one_or_self_of_dvd _ hsum with h | h <;> omega
  have hinf := Nat.infinite_setOf_prime
  obtain ⟨k, hk⟩ : ∃ k, Nat.count Nat.Prime ((B + 2)! + 2) = k := ⟨_, rfl⟩
  have hk1 : (B + 2)! + 2 ≤ Nat.nth Nat.Prime k := by
    rw [← hk]; exact (Nat.count_le_iff_le_nth hinf).mp le_rfl
  have hkprime : Nat.Prime (Nat.nth Nat.Prime k) := Nat.nth_mem_of_infinite hinf k
  have hkbig : (B + 2)! + B + 3 ≤ Nat.nth Nat.Prime k := by
    by_contra hcon
    exact hnp _ hk1 (by omega) hkprime
  have hkpos : 1 ≤ k := by
    have h2 : Nat.nth Nat.Prime 0 < (B + 2)! + 2 := by
      rw [Nat.nth_prime_zero_eq_two]; omega
    have h3 := (Nat.lt_nth_iff_count_lt hinf).mpr h2
    rw [hk] at h3
    omega
  have hlow : Nat.nth Nat.Prime (k - 1) < (B + 2)! + 2 := by
    refine (Nat.lt_nth_iff_count_lt hinf).mp ?_
    rw [hk]; omega
  refine ⟨k - 1, ?_⟩
  rw [show k - 1 + 1 = k from by omega]
  omega

/-- Prime gaps are unbounded along every tail. -/
