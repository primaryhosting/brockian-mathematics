/-
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction
/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive and distinct, and
the sum of the divisors of each, other than the number itself and `1`, is the other member;
equivalently `sigma m = sigma n = m + n + 1`. -/

theorem partner_of_prime_pow {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    ∃ b : ℕ, a = b + 1 ∧ 1 ≤ b ∧ n = p * (∑ i ∈ Finset.range b, p ^ i) ∧
      ¬ p ∣ (∑ i ∈ Finset.range b, p ^ i) := by
  obtain ⟨hm0, hn0, hne, hsm, hsn⟩ := h
  rw [sigma_one_prime_pow hp, Finset.sum_range_succ] at hsm
  have hsum : ∑ i ∈ Finset.range a, p ^ i = n + 1 := by omega
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := by
    cases a with
    | zero => simp at hsum
    | succ k => exact ⟨k, rfl⟩
  rw [geom_sum_succ] at hsum
  have hb : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp at hsum; omega
    · exact hb
  refine ⟨b, rfl, hb, by omega, ?_⟩
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [geom_sum_succ]
  intro hdvd
  have h1 : p ∣ 1 := (Nat.dvd_add_right ⟨_, rfl⟩).mp hdvd
  have h2 := Nat.dvd_one.mp h1
  have h3 := hp.two_le
  omega

