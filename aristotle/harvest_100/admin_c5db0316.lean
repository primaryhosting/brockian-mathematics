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
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

lemma IsBetrothedPair.symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h2, h1, ?_, ?_⟩ <;> omega

/-- Sanity check: `(48, 75)` is the smallest betrothed pair, so the notion is not vacuous. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-! ### Elementary facts about `σ` -/

lemma self_le_sigma {u : ℕ} (hu : 0 < u) : u ≤ σ 1 u := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (f := fun d => d) (by intros; positivity)
    (Nat.mem_divisors_self u hu.ne')

lemma two_mul_sigma_le {q : ℕ} : 2 * σ 1 q ≤ q * (q + 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hsub : q.divisors ⊆ Finset.range (q + 1) := by
    intro d hd
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.divisor_le hd))
  have h1 : σ 1 q ≤ ∑ i ∈ Finset.range (q + 1), i := by
    rw [sigma_one_apply]
    exact Finset.sum_le_sum_of_subset hsub
  have h2 : (∑ i ∈ Finset.range (q + 1), i) * 2 = (q + 1) * q :=
    Finset.sum_range_id_mul_two (q + 1)
  calc 2 * σ 1 q ≤ (∑ i ∈ Finset.range (q + 1), i) * 2 := by omega
    _ = (q + 1) * q := h2
    _ = q * (q + 1) := Nat.mul_comm _ _

lemma sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simp [pow_one, Finset.sum_range_succ] at this
  omega

/-- `2 σ(3^t) + 1 = 3^(t+1)`. -/
lemma two_mul_sigma_three_pow (t : ℕ) : 2 * σ 1 (3 ^ t) + 1 = 3 ^ (t + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h1 : σ 1 (3 ^ (t + 1)) = σ 1 (3 ^ t) + 3 ^ (t + 1) := by
        rw [sigma_one_apply_prime_pow (by norm_num), sigma_one_apply_prime_pow (by norm_num),
          Finset.sum_range_succ]
      rw [h1]
      have : (3:ℕ) ^ (t + 1 + 1) = 3 * 3 ^ (t + 1) := by ring
      omega

/-- Parity of a geometric sum with odd ratio. -/
lemma geom_sum_odd_parity {p : ℕ} (hp : Odd p) (k : ℕ) :
    (∑ i ∈ Finset.range k, p ^ i) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hodd : p ^ k % 2 = 1 := Nat.odd_iff.1 (hp.pow)
      rw [Finset.sum_range_succ]
      omega

lemma two_pow_geom (c : ℕ) : (∑ i ∈ Finset.range c, (2:ℕ) ^ i) + 1 = 2 ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Finset.sum_range_succ]
      have : (2:ℕ) ^ (c + 1) = 2 * 2 ^ c := by ring
      omega

/-! ### Structure of the partner of a prime power -/

/-- If `p ^ a` belongs to a betrothed pair with partner `n`, then `a = c + 1` with `c ≥ 1`
and `n = p * (1 + p + ⋯ + p ^ (c-1))`. -/
lemma partner_eq {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    ∃ c, 0 < c ∧ a = c + 1 ∧ n = p * ∑ i ∈ Finset.range c, p ^ i := by
  obtain ⟨-, hn, hsig, -⟩ := h
  rw [sigma_one_apply_prime_pow hp] at hsig
  match a with
  | 0 => simp at hsig
  | (c + 1) =>
      refine ⟨c, ?_, rfl, ?_⟩
      · rcases Nat.eq_zero_or_pos c with rfl | hc
        · simp [Finset.sum_range_succ] at hsig; omega
        · exact hc
      · have hexp : ∑ i ∈ Finset.range (c + 1 + 1), p ^ i
            = (p * ∑ i ∈ Finset.range c, p ^ i + 1) + p ^ (c + 1) := by
          rw [Finset.sum_range_succ, geom_sum_succ]
        rw [hexp] at hsig
        omega

/-- The partner is `p * S` with `S` coprime to `p`, so `σ n = (p+1) σ S`. -/
lemma sigma_partner {p c : ℕ} (hp : p.Prime) (hc : 0 < c) :
    σ 1 (p * ∑ i ∈ Finset.range c, p ^ i) = (p + 1) * σ 1 (∑ i ∈ Finset.range c, p ^ i) := by
  have hcop : Nat.Coprime p (∑ i ∈ Finset.range c, p ^ i) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [geom_sum_succ] at hdvd
    have : p ∣ 1 := (Nat.dvd_add_right (Dvd.intro _ rfl)).1 hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime hp]

/-! ### The base `2` case is impossible -/

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

lemma sigma_succ_ne {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (heq : σ 1 (p + 1) = 1 + p ^ 2) :
    False := by
  have hb : 2 * σ 1 (p + 1) ≤ (p + 1) * (p + 1 + 1) := two_mul_sigma_le
  rw [heq] at hb
  have hp3 : p ≤ 3 := by nlinarith
  have hp2 : 2 ≤ p := hp.two_le
  have : p = 3 := by
    rcases Nat.lt_or_ge p 3 with h | h
    · exfalso
      have : p = 2 := by omega
      rw [this] at hpodd
      exact (Nat.not_odd_iff_even.2 (by decide)) hpodd
    · omega
  subst this
  rw [show (3:ℕ) + 1 = 4 from rfl] at heq
  norm_num [show σ 1 4 = 7 from by decide] at heq

/-! ### Main theorem -/

/-- **Hagis–Lord, Proposition 4.** If a prime power `p ^ a` is a member of a betrothed
(quasi-amicable) pair with partner `n`, then `p` is odd, the exponent `a` is odd and larger
than `3`, and the partner `n` is even. -/
theorem primePower_member_structure {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    Odd p ∧ Odd a ∧ 3 < a ∧ Even n := by
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with rfl | h2
    · exact absurd h not_two_pow_member
    · exact h2
  obtain ⟨c, hc, rfl, rfl⟩ := partner_eq hp h
  set S : ℕ := ∑ i ∈ Finset.range c, p ^ i with hS
  obtain ⟨-, hnpos, hsig1, hsig2⟩ := h
  have hσn : σ 1 (p * S) = (p + 1) * σ 1 S := by rw [hS, sigma_partner hp hc]
  have hkey : (p + 1) * σ 1 S = ∑ i ∈ Finset.range (c + 1 + 1), p ^ i := by
    rw [← hσn, hsig2, ← hsig1, sigma_one_apply_prime_pow hp]
  -- `c` is even
  have hGpar : (∑ i ∈ Finset.range (c + 1 + 1), p ^ i) % 2 = c % 2 := by
    rw [geom_sum_odd_parity hpodd]
    omega
  have hceven : c % 2 = 0 := by
    have h2p : (2:ℕ) ∣ p + 1 := by
      obtain ⟨k, rfl⟩ := hpodd
      omega
    have hdvd : (2:ℕ) ∣ ∑ i ∈ Finset.range (c + 1 + 1), p ^ i := by
      rw [← hkey]
      exact Dvd.dvd.mul_right h2p _
    omega
  have hSpar : S % 2 = 0 := by rw [hS, geom_sum_odd_parity hpodd]; exact hceven
  refine ⟨hpodd, Nat.odd_iff.2 (by omega), ?_, ?_⟩
  · -- `c ≠ 2`
    have hcne : c ≠ 2 := by
      rintro rfl
      have hS2 : S = 1 + p := by
        rw [hS]
        simp [Finset.sum_range_succ, add_comm]
      have hexp : ∑ i ∈ Finset.range (2 + 1 + 1), p ^ i = (p + 1) * (1 + p ^ 2) := by
        simp [Finset.sum_range_succ]
        ring
      rw [hexp, hS2] at hkey
      have hcancel : σ 1 (1 + p) = 1 + p ^ 2 :=
        Nat.eq_of_mul_eq_mul_left (by omega) hkey
      rw [add_comm 1 p] at hcancel
      exact sigma_succ_ne hp hpodd hcancel
    omega
  · exact (Nat.even_iff.2 hSpar).mul_left p

/-- Both members of a betrothed pair cannot be prime powers. -/
theorem not_both_primePowers {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : IsBetrothedPair (p ^ a) (q ^ b)) : False := by
  obtain ⟨-, -, -, hev⟩ := primePower_member_structure hp h
  obtain ⟨hqodd, -, -, -⟩ := primePower_member_structure hq h.symm
  exact (Nat.not_odd_iff_even.2 hev) hqodd.pow

end Brockian.BetrothedNumbers

import Mathlib
import RequestProject.BetrothedPrimePower

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

