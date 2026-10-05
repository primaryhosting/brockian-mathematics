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
open scoped ArithmeticFunction.sigma

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
two distinct positive integers each of whose sum of divisors equals `m + n + 1`;
equivalently, the sum of the proper divisors of each member is the other member plus one. -/

lemma not_two_pow {a n : ℕ} (h : IsBetrothedPair (2 ^ a) n) : False := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  obtain ⟨k, hk1, rfl, hnk⟩ := partner_eq Nat.prime_two hn h1
  obtain ⟨u, hu⟩ : ∃ u, u = ∑ i ∈ Finset.range k, 2 ^ i := ⟨_, rfl⟩
  rw [← hu] at hnk
  have hu2 : u + 1 = 2 ^ k := by
    rw [hu]
    simpa using (Nat.geomSum_eq (le_refl 2) k).symm
  have hupos : 0 < u := by
    have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    omega
  have huodd : u % 2 = 1 := by
    have h2k : 2 ^ k % 2 = 0 := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp [pow_succ]
    omega
  have hcop : Nat.Coprime 2 u := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  have hsig2 : ∑ d ∈ (2 : ℕ).divisors, d = 3 := by decide
  have hsn : σ 1 (2 * u) = 3 * σ 1 u := by
    rw [sigma_one_apply, sigma_one_apply, hcop.sum_divisors_mul, hsig2]
  rw [hnk, hsn] at h2
  have hpow : 2 ^ (k + 1) = 2 * u + 2 := by rw [pow_succ]; omega
  have key : 3 * σ 1 u = 4 * u + 3 := by omega
  have hu9 : u = 9 := eq_nine_of_sigma_rel hupos key
  -- `2 ^ k = 10` is impossible
  have h2k : 2 ^ k = 10 := by omega
  have hk4 : k ≤ 3 := by
    by_contra hc
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> omega

/-- **Hagis–Lord, Proposition 4.**  If a prime power `p ^ a` is a member of a betrothed
(quasi-amicable) pair, then `p` is odd, the exponent `a` is odd and greater than `3`, and the
partner is even. -/
