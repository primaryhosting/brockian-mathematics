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

namespace Brockian
namespace BetrothedNumbers

open Finset
open scoped ArithmeticFunction.sigma

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, they are distinct,
and the sum of the divisors of each, other than the number itself and `1`, gives the other;
equivalently `σ m = σ n = m + n + 1`. -/

lemma prime_ne_two {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) : p ≠ 2 := by
  rintro rfl
  obtain ⟨k, rfl, rfl⟩ := partner_form hp h
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  have hodd : (∑ i ∈ range (k + 1), 2 ^ i) % 2 = 1 := by rw [geom_split]; omega
  have hcop : Nat.Coprime 2 (∑ i ∈ range (k + 1), 2 ^ i) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (fun hd => by omega)
  rw [sigma_prime_mul Nat.prime_two hcop] at h2
  have hpow : (∑ i ∈ range (k + 1), 2 ^ i) + 1 = 2 ^ (k + 1) := two_pow_geom (k + 1)
  have hpow2 : (2 : ℕ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
  have hkey : 3 * σ 1 (∑ i ∈ range (k + 1), 2 ^ i) = 4 * (∑ i ∈ range (k + 1), 2 ^ i) + 3 := by
    omega
  match k with
  | 0 => norm_num [Finset.sum_range_succ] at hkey
  | 1 =>
      norm_num [Finset.sum_range_succ] at hkey
      rw [show σ 1 3 = 4 by decide] at hkey
      omega
  | 2 =>
      norm_num [Finset.sum_range_succ] at hkey
      rw [show σ 1 7 = 8 by decide] at hkey
      omega
  | (k + 3) =>
      refine no_large_two_case ?_ hkey
      have h : ∑ i ∈ range 4, (2 : ℕ) ^ i ≤ ∑ i ∈ range (k + 3 + 1), 2 ^ i :=
        Finset.sum_le_sum_of_subset (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
      simpa [Finset.sum_range_succ] using h

