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
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧
    ArithmeticFunction.sigma 1 m = m + n + 1 ∧ ArithmeticFunction.sigma 1 n = m + n + 1

/-- Geometric sum identity in `ℕ`, in subtraction-free form. -/
lemma geom_sum_mul_succ (q a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), (q + 1) ^ i) * q + 1 = (q + 1) ^ (a + 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Finset.sum_range_succ, add_mul, pow_succ ((q+1)) (a+1)]
      nlinarith [ih]

/-- `σ (p ^ a) * (p - 1) < p ^ a * p` for a prime `p`. -/
lemma sigma_prime_pow_mul_pred_lt {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ArithmeticFunction.sigma 1 (p ^ a) * (p - 1) < p ^ a * p := by
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hs : ArithmeticFunction.sigma 1 ((q + 1) ^ a) = ∑ i ∈ Finset.range (a + 1), (q + 1) ^ i := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  rw [hs, Nat.add_sub_cancel, ← pow_succ]
  have := geom_sum_mul_succ q a
  omega

/-- Key abundancy bound: for `2 ≤ N`,
`σ N * ∏_{p ∣ N} (p - 1) < N * ∏_{p ∣ N} p`. -/
lemma sigma_mul_prod_pred_lt {N : ℕ} (hN : 2 ≤ N) :
    ArithmeticFunction.sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1) <
      N * ∏ p ∈ N.primeFactors, p := by
  have hN0 : N ≠ 0 := by omega
  have hNe : N.primeFactors.Nonempty := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := N) (by omega)
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpd, hN0⟩⟩
  have hsig : ArithmeticFunction.sigma 1 N =
      ∏ p ∈ N.primeFactors, ArithmeticFunction.sigma 1 (p ^ N.factorization p) := by
    rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
      (ArithmeticFunction.isMultiplicative_sigma) hN0]
    rw [Finsupp.prod, Nat.support_factorization]
  have hNprod : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN0]
    rw [Finsupp.prod, Nat.support_factorization]
  calc ArithmeticFunction.sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1)
      = ∏ p ∈ N.primeFactors,
          (ArithmeticFunction.sigma 1 (p ^ N.factorization p) * (p - 1)) := by
        rw [hsig, Finset.prod_mul_distrib]
    _ < ∏ p ∈ N.primeFactors, (p ^ N.factorization p * p) := ?_
    _ = N * ∏ p ∈ N.primeFactors, p := by
        rw [Finset.prod_mul_distrib, ← hNprod]
  refine Finset.prod_lt_prod_of_nonempty ?_ ?_ hNe
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have h1 : 0 < ArithmeticFunction.sigma 1 (p ^ N.factorization p) := by
      rw [ArithmeticFunction.sigma_one_apply]
      have hne : p ^ N.factorization p ≠ 0 := pow_ne_zero _ hpp.pos.ne'
      exact Finset.sum_pos' (by intro i _; exact Nat.zero_le i)
        ⟨p ^ N.factorization p, Nat.mem_divisors_self _ hne,
          pow_pos hpp.pos _⟩
    have h2 : 0 < p - 1 := by have := hpp.two_le; omega
    exact Nat.mul_pos h1 h2
  · intro p hp
    exact sigma_prime_pow_mul_pred_lt (Nat.prime_of_mem_primeFactors hp) _

/-- Sorted version of the three–prime bound. -/
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
lemma three_primes_bound {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a * b * c ≤ 4 * ((a - 1) * ((b - 1) * (c - 1))) := by
  have main : ∀ x y z : ℕ, x.Prime → y.Prime → z.Prime → x < y → y < z →
      x * y * z ≤ 4 * ((x - 1) * ((y - 1) * (z - 1))) := by
    intro x y z hx hy hz hxy hyz
    exact three_primes_bound_sorted hx hy hz hxy hyz
  rcases Nat.lt_or_ge a b with h1 | h1
  · rcases Nat.lt_or_ge b c with h2 | h2
    · have := main a b c ha hb hc h1 h2; linarith [this]
    · have h2' : c < b := by omega
      rcases Nat.lt_or_ge a c with h3 | h3
      · have := main a c b ha hc hb h3 h2'
        calc a * b * c = a * c * b := by ring
          _ ≤ 4 * ((a-1) * ((c-1) * (b-1))) := this
          _ = 4 * ((a-1) * ((b-1) * (c-1))) := by ring
      · have h3' : c < a := by omega
        have := main c a b hc ha hb h3' h1
        calc a * b * c = c * a * b := by ring
          _ ≤ 4 * ((c-1) * ((a-1) * (b-1))) := this
          _ = 4 * ((a-1) * ((b-1) * (c-1))) := by ring
  · have h1' : b < a := by omega
    rcases Nat.lt_or_ge a c with h2 | h2
    · have := main b a c hb ha hc h1' h2
      calc a * b * c = b * a * c := by ring
        _ ≤ 4 * ((b-1) * ((a-1) * (c-1))) := this
        _ = 4 * ((a-1) * ((b-1) * (c-1))) := by ring
    · have h2' : c < a := by omega
      rcases Nat.lt_or_ge b c with h3 | h3
      · have := main b c a hb hc ha h3 h2'
        calc a * b * c = b * c * a := by ring
          _ ≤ 4 * ((b-1) * ((c-1) * (a-1))) := this
          _ = 4 * ((a-1) * ((b-1) * (c-1))) := by ring
      · have h3' : c < b := by omega
        have := main c b a hc hb ha h3' h1'
        calc a * b * c = c * b * a := by ring
          _ ≤ 4 * ((c-1) * ((b-1) * (a-1))) := this
          _ = 4 * ((a-1) * ((b-1) * (c-1))) := by ring

/-- If a finite set of primes has at most three elements then
`∏ p ≤ 4 * ∏ (p - 1)`. -/
lemma prod_le_four_mul_prod_pred {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    ∏ p ∈ S, p ≤ 4 * ∏ p ∈ S, (p - 1) := by
  interval_cases h : S.card
  · rw [Finset.card_eq_zero] at h; subst h; simp
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    have ha := hS a (by simp)
    have := ha.two_le
    simp only [Finset.prod_singleton]
    omega
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have ha := hS a (by simp)
    have hb := hS b (by simp)
    have ha2 := ha.two_le
    have hb2 := hb.two_le
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    -- one of a, b is ≥ 3
    rcases Nat.lt_or_ge a 3 with h3 | h3
    · have ha2' : a = 2 := by omega
      subst ha2'
      have hb3 : 3 ≤ b := by omega
      obtain ⟨B, rfl⟩ : ∃ B, b = B + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      omega
    · obtain ⟨A, rfl⟩ : ∃ A, a = A + 1 := ⟨a - 1, by omega⟩
      obtain ⟨B, rfl⟩ : ∃ B, b = B + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith [Nat.mul_le_mul (show 2 ≤ A by omega) (show 1 ≤ B by omega)]
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
    have ha := hS a (by simp)
    have hb := hS b (by simp)
    have hc := hS c (by simp)
    rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
      Finset.prod_singleton, Finset.prod_insert (by simp [hab, hac]),
      Finset.prod_insert (by simp [hbc]), Finset.prod_singleton]
    have := three_primes_bound ha hb hc hab hac hbc
    calc a * (b * c) = a * b * c := by ring
      _ ≤ 4 * ((a - 1) * ((b - 1) * (c - 1))) := this

/-- **Hagis–Lord, Proposition 2.** If `m` and `n` are coprime betrothed numbers then
`m * n` has at least four distinct prime factors. -/
theorem coprime_pair_four_primeFactors {m n : ℕ} (h : Betrothed m n)
    (hmn : Nat.Coprime m n) : 4 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  set N := m * n with hNdef
  have hN0 : N ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  -- σ N = (m + n + 1) ^ 2
  have hsigN : ArithmeticFunction.sigma 1 N = (m + n + 1) ^ 2 := by
    rw [hNdef, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hmn, hsm, hsn, sq]
  -- abundancy: σ N > 4 N
  have habund : 4 * N < ArithmeticFunction.sigma 1 N := by
    rw [hsigN, hNdef]
    zify
    nlinarith [sq_nonneg ((m : ℤ) - (n : ℤ)), (show (0:ℤ) < (m:ℤ) by exact_mod_cast hm),
      (show (0:ℤ) < (n:ℤ) by exact_mod_cast hn)]
  have hN2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h | h
    · interval_cases N
      · simp at hN0
      · simp at habund
    · exact h
  by_contra hcard
  push_neg at hcard
  have hcard3 : N.primeFactors.card ≤ 3 := by omega
  have hB := prod_le_four_mul_prod_pred (S := N.primeFactors)
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard3
  have hA := sigma_mul_prod_pred_lt hN2
  have hpos : 0 < ∏ p ∈ N.primeFactors, (p - 1) := by
    refine Finset.prod_pos ?_
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  -- 4 * N * ∏ (p-1) < N * ∏ p ≤ N * 4 * ∏ (p-1) : contradiction
  have h1 : 4 * N * ∏ p ∈ N.primeFactors, (p - 1) <
      N * ∏ p ∈ N.primeFactors, p :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (le_of_lt habund)) hA
  have h2 : N * ∏ p ∈ N.primeFactors, p ≤ N * (4 * ∏ p ∈ N.primeFactors, (p - 1)) :=
    Nat.mul_le_mul_left _ hB
  have hNpos : 0 < N := by omega
  nlinarith [h1, h2, hpos, hNpos]

end BetrothedNumbers
end Brockian

