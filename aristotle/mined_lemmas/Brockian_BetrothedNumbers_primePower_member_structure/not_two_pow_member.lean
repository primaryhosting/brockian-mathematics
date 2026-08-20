import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `IsBetrothedPair m n` : `m` and `n` form a betrothed (quasi-amicable) pair, i.e. the sum of
the nontrivial divisors (all divisors except `1` and the number itself) of each equals the other.
Equivalently `σ m = σ n = m + n + 1`.

The classical definition additionally requires `m ≠ n`; that hypothesis is not needed for any of
the results below, so it is omitted here (making the statements slightly stronger). -/

lemma not_two_pow_member {a n : ℕ} (h : IsBetrothedPair (2 ^ a) n) : False := by
  obtain ⟨c, hc, rfl, rfl⟩ := partner_eq Nat.prime_two h
  set S : ℕ := ∑ i ∈ Finset.range c, (2:ℕ) ^ i with hS
  obtain ⟨-, hnpos, hsig1, hsig2⟩ := h
  have hSc : S + 1 = 2 ^ c := two_pow_geom c
  have hSpos : 0 < S := by
    have : (2:ℕ) ^ 1 ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc
    simp only [pow_one] at this
    omega
  -- the fundamental equation `3 σ S = 4 S + 3`
  have hσn : σ 1 (2 * S) = 3 * σ 1 S := by
    rw [hS, sigma_partner Nat.prime_two hc]
  have hG : σ 1 ((2:ℕ) ^ (c + 1)) = 4 * S + 3 := by
    rw [sigma_one_apply_prime_pow Nat.prime_two]
    have e2 : (∑ i ∈ Finset.range (c + 1 + 1), (2:ℕ) ^ i) + 1 = 2 ^ (c + 1 + 1) :=
      two_pow_geom (c + 1 + 1)
    have e3 : (2:ℕ) ^ (c + 1 + 1) = 4 * 2 ^ c := by ring
    omega
  have hkey : 3 * σ 1 S = 4 * S + 3 := by
    rw [hσn] at hsig2
    omega
  -- extract the `3`-part of `S`
  have h3S : (3:ℕ) ∣ S := by
    have h1 : (3:ℕ) ∣ 4 * S + 3 := hkey ▸ Dvd.intro _ rfl
    omega
  set t : ℕ := S.factorization 3 with ht
  set X : ℕ := 3 ^ t with hX
  set u : ℕ := S / 3 ^ t with hu
  have htpos : 0 < t := (Nat.Prime.factorization_pos_of_dvd (by norm_num) hSpos.ne' h3S)
  have hXu : X * u = S := Nat.ordProj_mul_ordCompl_eq_self S 3
  have hupos : 0 < u := Nat.ordCompl_pos 3 hSpos.ne'
  have hcop : Nat.Coprime X u :=
    Nat.Coprime.pow_left t (Nat.coprime_ordCompl (by norm_num) hSpos.ne')
  have hσS : σ 1 S = σ 1 X * σ 1 u := by
    rw [← hXu, isMultiplicative_sigma.map_mul_of_coprime hcop]
  have hA : 2 * σ 1 X + 1 = 3 * X := by
    have hg := two_mul_sigma_three_pow t
    rw [pow_succ, ← hX] at hg
    omega
  have hsu : u ≤ σ 1 u := self_le_sigma hupos
  have heq : 3 * (σ 1 X * σ 1 u) = 4 * (X * u) + 3 := by rw [hXu, ← hσS]; exact hkey
  rcases Nat.lt_or_ge t 2 with h1 | h2
  · -- `t = 1`, i.e. `3 ‖ S`
    have ht1 : t = 1 := by omega
    have hX3 : X = 3 := by rw [hX, ht1]; norm_num
    rw [hX3] at hA heq
    have hσX : σ 1 3 = 4 := by omega
    rw [hσX] at heq
    omega
  · -- `t ≥ 2`
    have hX9 : 9 ≤ X := by
      calc (9:ℕ) = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) h2
    have hid : 9 * X * σ 1 u = 8 * X * u + 6 + 3 * σ 1 u := by nlinarith [hA, heq]
    have hu1 : u = 1 := by nlinarith [hid, hsu, hupos, hX9]
    rw [hu1] at hid
    simp only [ArithmeticFunction.sigma_one, mul_one] at hid
    have hX' : X = 9 := by omega
    have hS9 : S = 9 := by rw [← hXu, hX', hu1]
    -- but `S + 1 = 2 ^ c` cannot be `10`
    have h10 : (2:ℕ) ^ c = 10 := by omega
    have h5 : (5:ℕ) ∣ 2 ^ c := ⟨2, by omega⟩
    have := Nat.Prime.dvd_of_dvd_pow (p := 5) (by norm_num) h5
    norm_num at this

/-! ### The exponent cannot be `3` -/

