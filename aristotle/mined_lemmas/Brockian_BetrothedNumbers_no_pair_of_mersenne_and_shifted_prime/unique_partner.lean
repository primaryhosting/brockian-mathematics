/-
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open scoped ArithmeticFunction.sigma

namespace Brockian
namespace BetrothedNumbers

/-- Two natural numbers `m` and `n` form a *betrothed* (quasi-amicable) pair when the sum of
divisors of each of them equals `m + n + 1`. -/

theorem unique_partner {k p m : ℕ} (hk : 2 ≤ k) (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (2 ^ k * p) m) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨h1, -⟩ := h
  rw [sigma_one_two_pow_mul_odd_prime hp hodd] at h1
  have hQ : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hk4 : 4 ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  set Q : ℕ := 2 ^ k with hQdef
  have hexp : (2 * Q - 1) * (p + 1) = 2 * Q * p + 2 * Q - p - 1 := by
    cases Nat.exists_eq_add_of_le (show 1 ≤ 2 * Q by omega) with
    | intro c hc =>
        have : 2 * Q = c + 1 := by omega
        rw [this]
        simp only [Nat.add_sub_cancel]
        ring_nf
        omega
  have hexp2 : (Q - 1) * (p + 2) = Q * p + 2 * Q - p - 2 := by
    cases Nat.exists_eq_add_of_le (show 1 ≤ Q by omega) with
    | intro c hc =>
        have : Q = c + 1 := by omega
        rw [this]
        simp only [Nat.add_sub_cancel]
        ring_nf
        omega
  rw [hQ, hexp] at h1
  rw [hexp2]
  have hQp : Q ≤ Q * p := Nat.le_mul_of_pos_right _ hp.pos
  omega

/-- **Target.** Let `k ≥ 2` and let `p` be an odd prime such that both `2 ^ k - 1` and `p + 2`
are prime.  Then no natural number forms a betrothed pair with `2 ^ k * p`. -/
