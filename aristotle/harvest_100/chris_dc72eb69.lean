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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Betrothed (quasi-amicable) numbers

Two distinct positive integers `m ≠ n` are *betrothed* (or *quasi-amicable*) when each is the
sum of the non-trivial proper divisors of the other, i.e.

  `σ m = σ n = m + n + 1`,

where `σ = σ₁` is the sum-of-divisors function.  Examples are `(48, 75)`, `(140, 195)`,
`(1050, 1925)`, ....  In every known example the two members have *opposite* parity, and whether a
betrothed pair of the *same* parity exists is an open problem.

This file states that open problem as `SameParityBetrothedExists` and proves everything about it
that we can:

* `betrothed_48_75` : betrothed pairs do exist (and this one has opposite parity);
* `odd_sigma_iff_isSquare_of_odd` : for odd `n`, `σ n` is odd iff `n` is a perfect square;
* `sq_or_two_mul_sq_of_odd_sigma` : if `σ n` is odd (`n ≠ 0`) then `n = k ^ 2` or `n = 2 * k ^ 2`;
* `sameParity_structure` : both members of a same-parity betrothed pair are of the form
  `k ^ 2` or `2 * k ^ 2`, and if they are odd they are perfect squares;
* `no_sameParity_betrothed_lt_500` : a kernel-checked verification that no same-parity betrothed
  pair has a member below `500`;
* `sameParityBetrothedExists_reduction` : the resulting conditional reduction of the open problem.
-/

namespace Brockian.BetrothedNumbers

open scoped ArithmeticFunction.sigma

/-- `Betrothed m n` : `m` and `n` are distinct positive integers each of which is the sum of the
non-trivial proper divisors of the other, i.e. `σ m = σ n = m + n + 1`.  (Such pairs are also
called *quasi-amicable* or *reduced amicable* pairs.) -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- The (open) statement that there is a betrothed pair whose two members have the same parity.
All known betrothed pairs consist of one even and one odd number. -/
def SameParityBetrothedExists : Prop :=
  ∃ m n : ℕ, Betrothed m n ∧ m % 2 = n % 2

theorem betrothed_comm {m n : ℕ} (h : Betrothed m n) : Betrothed n m := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  refine ⟨hn, hm, hne.symm, ?_, ?_⟩ <;> omega

/-- `(48, 75)` is a betrothed pair: `σ 48 = σ 75 = 124 = 48 + 75 + 1`. -/
theorem betrothed_48_75 : Betrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-- The betrothed pair `(48, 75)` has members of opposite parity, as do all known ones. -/
theorem betrothed_48_75_not_sameParity : 48 % 2 ≠ 75 % 2 := by decide

/-! ### Parity of the sum-of-divisors function -/

/-- For an odd prime `p`, `σ (p ^ e) ≡ e + 1 [MOD 2]`. -/
theorem sigma_prime_pow_mod_two {p : ℕ} (e : ℕ) (hp : p.Prime) (hp2 : p % 2 = 1) :
    σ 1 (p ^ e) % 2 = (e + 1) % 2 := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp, Finset.sum_nat_mod]
  have h : ∀ i ∈ Finset.range (e + 1), p ^ i % 2 = 1 := by
    intro i _
    simp [Nat.pow_mod, hp2]
  rw [Finset.sum_congr rfl h]
  simp

/-- If `n` is odd and `σ n` is odd, then `n` is a perfect square. -/
theorem isSquare_of_odd_of_odd_sigma (n : ℕ) (hn : n % 2 = 1) (hs : σ 1 n % 2 = 1) :
    IsSquare n := by
  induction n using Nat.recOnPrimePow with
  | zero => simp at hn
  | one => exact ⟨1, rfl⟩
  | prime_pow_mul a p k hp hpa hk ih =>
    have hp2 : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with rfl | h
      · exact absurd hn (by
          have : 2 ∣ 2 ^ k * a := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) a
          omega)
      · exact h
    have ha2 : a % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one a with h | h
      · have h2 : (2 : ℕ) ∣ a := by omega
        have : (2 : ℕ) ∣ p ^ k * a := h2.mul_left _
        omega
      · exact h
    have hcop : Nat.Coprime (p ^ k) a := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa).pow_left _
    have hmul : σ 1 (p ^ k * a) = σ 1 (p ^ k) * σ 1 a :=
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
    rw [hmul, Nat.mul_mod] at hs
    have hs2 : σ 1 a % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (σ 1 a) with h | h
      · rw [h] at hs; simp at hs
      · exact h
    have hs1 : σ 1 (p ^ k) % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (σ 1 (p ^ k)) with h | h
      · rw [h] at hs; simp at hs
      · exact h
    have hk2 : k % 2 = 0 := by
      have := sigma_prime_pow_mod_two k hp hp2
      omega
    obtain ⟨t, ht⟩ := ih ha2 hs2
    refine ⟨p ^ (k / 2) * t, ?_⟩
    have hpk : p ^ k = p ^ (k / 2) * p ^ (k / 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [ht, hpk]
    ring

/-- If `t` is odd then `σ (t ^ 2)` is odd. -/
theorem odd_sigma_sq_of_odd (t : ℕ) (ht : t % 2 = 1) : σ 1 (t ^ 2) % 2 = 1 := by
  induction t using Nat.recOnPrimePow with
  | zero => simp at ht
  | one => simp
  | prime_pow_mul a p k hp hpa hk ih =>
    have hp2 : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with rfl | h
      · exact absurd ht (by
          have : 2 ∣ 2 ^ k * a := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) a
          omega)
      · exact h
    have ha2 : a % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one a with h | h
      · have h2 : (2 : ℕ) ∣ a := by omega
        have : (2 : ℕ) ∣ p ^ k * a := h2.mul_left _
        omega
      · exact h
    have hcop : Nat.Coprime (p ^ (2 * k)) (a ^ 2) :=
      (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa).pow_left _).pow_right _
    have hrw : (p ^ k * a) ^ 2 = p ^ (2 * k) * a ^ 2 := by ring
    rw [hrw, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, Nat.mul_mod,
      sigma_prime_pow_mod_two (2 * k) hp hp2, ih ha2]
    omega

/-- For odd `n`, `σ n` is odd exactly when `n` is a perfect square. -/
theorem odd_sigma_iff_isSquare_of_odd {n : ℕ} (hn : n % 2 = 1) :
    σ 1 n % 2 = 1 ↔ IsSquare n := by
  refine ⟨isSquare_of_odd_of_odd_sigma n hn, ?_⟩
  rintro ⟨t, rfl⟩
  have ht : t % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have h2 : (2 : ℕ) ∣ t := by omega
      have : (2 : ℕ) ∣ t * t := h2.mul_left _
      omega
    · exact h
  have hsq : t * t = t ^ 2 := by ring
  rw [hsq]
  exact odd_sigma_sq_of_odd t ht

/-- If `σ n` is odd (and `n ≠ 0`) then `n` is a square or twice a square. -/
theorem sq_or_two_mul_sq_of_odd_sigma {n : ℕ} (hn : n ≠ 0) (hs : σ 1 n % 2 = 1) :
    ∃ k, n = k ^ 2 ∨ n = 2 * k ^ 2 := by
  set e := n.factorization 2 with he
  set u := ordCompl[2] n with hu
  have hun : 2 ^ e * u = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hnd : ¬(2 ∣ u) := Nat.not_dvd_ordCompl Nat.prime_two hn
  have hu2 : u % 2 = 1 := by omega
  have hcop : Nat.Coprime (2 ^ e) u := (Nat.coprime_ordCompl Nat.prime_two hn).pow_left _
  have hmul : σ 1 (2 ^ e * u) = σ 1 (2 ^ e) * σ 1 u :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [hun] at hmul
  rw [hmul, Nat.mul_mod] at hs
  have hsu : σ 1 u % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (σ 1 u) with h | h
    · rw [h] at hs; simp at hs
    · exact h
  obtain ⟨t, ht⟩ := isSquare_of_odd_of_odd_sigma u hu2 hsu
  rcases Nat.even_or_odd e with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨2 ^ j * t, Or.inl (by rw [← hun, ht, hj]; ring)⟩
  · exact ⟨2 ^ j * t, Or.inr (by rw [← hun, ht, hj]; ring)⟩

/-! ### Consequences for same-parity betrothed pairs -/

/-- In a same-parity betrothed pair both sums of divisors are odd (they equal the odd number
`m + n + 1`). -/
theorem odd_sigma_of_betrothed_of_sameParity {m n : ℕ} (h : Betrothed m n) (hpar : m % 2 = n % 2) :
    σ 1 m % 2 = 1 ∧ σ 1 n % 2 = 1 := by
  obtain ⟨-, -, -, h1, h2⟩ := h
  omega

/-- **Structure theorem.**  Each member of a same-parity betrothed pair is a perfect square or
twice a perfect square. -/
theorem sameParity_structure {m n : ℕ} (h : Betrothed m n) (hpar : m % 2 = n % 2) :
    (∃ a, m = a ^ 2 ∨ m = 2 * a ^ 2) ∧ (∃ b, n = b ^ 2 ∨ n = 2 * b ^ 2) := by
  have hm : 0 < m := h.1
  have hn : 0 < n := h.2.1
  obtain ⟨hsm, hsn⟩ := odd_sigma_of_betrothed_of_sameParity h hpar
  exact ⟨sq_or_two_mul_sq_of_odd_sigma (by omega) hsm,
    sq_or_two_mul_sq_of_odd_sigma (by omega) hsn⟩

/-- An odd-odd betrothed pair would consist of two perfect squares. -/
theorem sameParity_odd_isSquare {m n : ℕ} (h : Betrothed m n) (hm : m % 2 = 1) (hn : n % 2 = 1) :
    IsSquare m ∧ IsSquare n := by
  obtain ⟨hsm, hsn⟩ := odd_sigma_of_betrothed_of_sameParity h (by omega)
  exact ⟨isSquare_of_odd_of_odd_sigma m hm hsm, isSquare_of_odd_of_odd_sigma n hn hsn⟩

/-- The two members of a same-parity betrothed pair are either both odd squares, or both even. -/
theorem sameParity_odd_squares_or_both_even {m n : ℕ} (h : Betrothed m n) (hpar : m % 2 = n % 2) :
    (IsSquare m ∧ IsSquare n) ∨ (m % 2 = 0 ∧ n % 2 = 0) := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · exact Or.inr ⟨hm, by omega⟩
  · exact Or.inl (sameParity_odd_isSquare h hm (by omega))

/-! ### A finite verification -/

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
private theorem sameParity_check_500 : ∀ m ∈ Finset.range 500, 0 < m →
    (σ 1 (σ 1 m - m - 1) = m + (σ 1 m - m - 1) + 1 ∧ m ≠ σ 1 m - m - 1) →
      m % 2 ≠ (σ 1 m - m - 1) % 2 := by decide

/-- Kernel-checked: no betrothed pair with a member below `500` has both members of the same
parity. -/
theorem no_sameParity_betrothed_lt_500 {m n : ℕ} (h : Betrothed m n) (hm : m < 500) :
    m % 2 ≠ n % 2 := by
  obtain ⟨hm0, hn0, hne, h1, h2⟩ := h
  have hn : n = σ 1 m - m - 1 := by omega
  subst hn
  exact sameParity_check_500 m (Finset.mem_range.mpr hm) hm0 ⟨h2, hne⟩

/-- **Conditional reduction of the open problem.**  If a same-parity betrothed pair exists at all,
then there is one whose members both exceed `500`, both of which are of the form `k ^ 2` or
`2 * k ^ 2`, and which are moreover both perfect squares in the odd-odd case. -/
theorem sameParityBetrothedExists_reduction (H : SameParityBetrothedExists) :
    ∃ m n : ℕ, Betrothed m n ∧ m % 2 = n % 2 ∧ 500 ≤ m ∧ 500 ≤ n ∧
      (∃ a, m = a ^ 2 ∨ m = 2 * a ^ 2) ∧ (∃ b, n = b ^ 2 ∨ n = 2 * b ^ 2) ∧
      ((IsSquare m ∧ IsSquare n) ∨ (m % 2 = 0 ∧ n % 2 = 0)) := by
  obtain ⟨m, n, h, hpar⟩ := H
  have hm : 500 ≤ m := by
    by_contra hlt
    exact no_sameParity_betrothed_lt_500 h (by omega) hpar
  have hn : 500 ≤ n := by
    by_contra hlt
    exact no_sameParity_betrothed_lt_500 (betrothed_comm h) (by omega) hpar.symm
  obtain ⟨hstm, hstn⟩ := sameParity_structure h hpar
  exact ⟨m, n, h, hpar, hm, hn, hstm, hstn, sameParity_odd_squares_or_both_even h hpar⟩

end Brockian.BetrothedNumbers

