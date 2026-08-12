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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian

namespace BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- Geometric-sum identity in `ℕ`: `(1 + p + ⋯ + p ^ a) * (p - 1) + 1 = p ^ (a + 1)`. -/
lemma geom_sum_mul_pred_add_one {p : ℕ} (hp : 1 ≤ p) (a : ℕ) :
    (∑ k ∈ Finset.range (a + 1), p ^ k) * (p - 1) + 1 = p ^ (a + 1) := by
  have h := geom_sum_mul (p : ℤ) (a + 1)
  zify [hp]
  linarith [h]

/-- For a prime power, `σ (p ^ a) * (p - 1) < p ^ a * p`. -/
lemma sigma_prime_pow_mul_pred_lt {p : ℕ} (hp : p.Prime) (a : ℕ) :
    σ 1 (p ^ a) * (p - 1) < p ^ a * p := by
  have h := geom_sum_mul_pred_add_one hp.one_lt.le a
  rw [sigma_one_apply_prime_pow hp]
  have : p ^ a * p = p ^ (a + 1) := by ring
  omega

/-- Strict abundancy bound: `σ n * ∏_{p ∣ n} (p - 1) < n * ∏_{p ∣ n} p` for `n > 1`. -/
lemma sigma_mul_prod_pred_lt {n : ℕ} (hn : 1 < n) :
    σ 1 n * ∏ p ∈ n.primeFactors, (p - 1) < n * ∏ p ∈ n.primeFactors, p := by
  have hn0 : n ≠ 0 := by omega
  have hsig : σ 1 n = ∏ p ∈ n.primeFactors, σ 1 (p ^ n.factorization p) := by
    rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]
    refine Finset.prod_congr rfl ?_
    intro p hp
    rw [sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)]
    simp
  have hnprod : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
    rfl
  rw [hsig, ← Finset.prod_mul_distrib]
  have hrhs : n * ∏ p ∈ n.primeFactors, p
      = ∏ p ∈ n.primeFactors, (p ^ n.factorization p * p) := by
    rw [Finset.prod_mul_distrib, ← hnprod]
  rw [hrhs]
  refine Finset.prod_lt_prod_of_nonempty ?_ ?_ (Nat.nonempty_primeFactors.mpr hn)
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h1 : 0 < σ 1 (p ^ n.factorization p) :=
      ArithmeticFunction.sigma_pos 1 _ (pow_ne_zero _ hpp.pos.ne')
    have h2 : 0 < p - 1 := by have := hpp.two_le; omega
    exact Nat.mul_pos h1 h2
  · intro p hp
    exact sigma_prime_pow_mul_pred_lt (Nat.prime_of_mem_primeFactors hp) _

/-- Two distinct primes: `a * b ≤ 4 * ((a-1) * (b-1))`, given `2 ≤ a`, `3 ≤ b`. -/
lemma two_bound {a b : ℕ} (ha : 2 ≤ a) (hb : 3 ≤ b) : a * b ≤ 4 * ((a - 1) * (b - 1)) := by
  obtain ⟨x, rfl⟩ : ∃ x, a = 2 + x := ⟨a - 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = 3 + y := ⟨b - 3, by omega⟩
  simp only [show 2 + x - 1 = 1 + x by omega, show 3 + y - 1 = 2 + y by omega]
  have h : 4 * ((1 + x) * (2 + y)) = (2 + x) * (3 + y) + (2 + 2 * y + 5 * x + 3 * (x * y)) := by
    ring
  omega

/-- Three distinct primes: `a * b * c ≤ 4 * ((a-1)*(b-1)*(c-1))`, given `2 ≤ a`, `3 ≤ b`, `5 ≤ c`. -/
lemma three_bound {a b c : ℕ} (ha : 2 ≤ a) (hb : 3 ≤ b) (hc : 5 ≤ c) :
    a * b * c ≤ 4 * ((a - 1) * (b - 1) * (c - 1)) := by
  obtain ⟨x, rfl⟩ : ∃ x, a = 2 + x := ⟨a - 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = 3 + y := ⟨b - 3, by omega⟩
  obtain ⟨z, rfl⟩ : ∃ z, c = 5 + z := ⟨c - 5, by omega⟩
  simp only [show 2 + x - 1 = 1 + x by omega, show 3 + y - 1 = 2 + y by omega,
    show 5 + z - 1 = 4 + z by omega]
  have h : 4 * ((1 + x) * (2 + y) * (4 + z)) =
      (2 + x) * (3 + y) * (5 + z) +
        (2 + 6 * y + 17 * x + 11 * (x * y) + 2 * z + 2 * (y * z) + 5 * (x * z) +
          3 * (x * y * z)) := by ring
  omega

/-- A prime larger than another prime is at least `3`. -/
lemma three_le_of_prime_lt {p q : ℕ} (hq : q.Prime) (hp : 2 ≤ p) (h : p < q) : 3 ≤ q := by
  have := hq.two_le; omega

/-- A prime larger than `3` is at least `5`. -/
lemma five_le_of_prime_lt {q r : ℕ} (hr : r.Prime) (hq : 3 ≤ q) (h : q < r) : 5 ≤ r := by
  have h4 : r ≠ 4 := by rintro rfl; norm_num at hr
  omega

/-- Symmetric two-prime version of `two_bound`. -/
lemma two_bound_sym {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b) :
    a * b ≤ 4 * ((a - 1) * (b - 1)) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact two_bound ha.two_le (three_le_of_prime_lt hb ha.two_le h)
  · calc a * b = b * a := by ring
      _ ≤ 4 * ((b - 1) * (a - 1)) := two_bound hb.two_le (three_le_of_prime_lt ha hb.two_le h)
      _ = 4 * ((a - 1) * (b - 1)) := by ring

/-- Symmetric three-prime version of `three_bound`. -/
lemma three_bound_sym {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a * b * c ≤ 4 * ((a - 1) * (b - 1) * (c - 1)) := by
  have key : ∀ x y z : ℕ, x.Prime → y.Prime → z.Prime → x < y → y < z →
      x * y * z ≤ 4 * ((x - 1) * (y - 1) * (z - 1)) := by
    intro x y z hx hy hz hxy hyz
    exact three_bound hx.two_le (three_le_of_prime_lt hy hx.two_le hxy)
      (five_le_of_prime_lt hz (three_le_of_prime_lt hy hx.two_le hxy) hyz)
  rcases lt_trichotomy a b with h1 | h1 | h1
  · rcases lt_trichotomy b c with h2 | h2 | h2
    · exact key a b c ha hb hc h1 h2
    · exact absurd h2 hbc
    · rcases lt_trichotomy a c with h3 | h3 | h3
      · calc a * b * c = a * c * b := by ring
          _ ≤ 4 * ((a - 1) * (c - 1) * (b - 1)) := key a c b ha hc hb h3 h2
          _ = 4 * ((a - 1) * (b - 1) * (c - 1)) := by ring
      · exact absurd h3 hac
      · calc a * b * c = c * a * b := by ring
          _ ≤ 4 * ((c - 1) * (a - 1) * (b - 1)) := key c a b hc ha hb h3 h1
          _ = 4 * ((a - 1) * (b - 1) * (c - 1)) := by ring
  · exact absurd h1 hab
  · rcases lt_trichotomy a c with h2 | h2 | h2
    · calc a * b * c = b * a * c := by ring
        _ ≤ 4 * ((b - 1) * (a - 1) * (c - 1)) := key b a c hb ha hc h1 h2
        _ = 4 * ((a - 1) * (b - 1) * (c - 1)) := by ring
    · exact absurd h2 hac
    · rcases lt_trichotomy b c with h3 | h3 | h3
      · calc a * b * c = b * c * a := by ring
          _ ≤ 4 * ((b - 1) * (c - 1) * (a - 1)) := key b c a hb hc ha h3 h2
          _ = 4 * ((a - 1) * (b - 1) * (c - 1)) := by ring
      · exact absurd h3 hbc
      · calc a * b * c = c * b * a := by ring
          _ ≤ 4 * ((c - 1) * (b - 1) * (a - 1)) := key c b a hc hb ha h3 h1
          _ = 4 * ((a - 1) * (b - 1) * (c - 1)) := by ring

/-- For at most three distinct primes, `∏ p ≤ 4 * ∏ (p - 1)`. -/
lemma prod_le_four_mul_prod_pred {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    ∏ p ∈ S, p ≤ 4 * ∏ p ∈ S, (p - 1) := by
  have h : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases h with h | h | h | h
  · rw [Finset.card_eq_zero] at h; subst h; simp
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    simp only [Finset.prod_singleton]
    have := (hS a (by simp)).two_le
    omega
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    exact two_bound_sym (hS a (by simp)) (hS b (by simp)) hab
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
    have ha := hS a (by simp)
    have hb := hS b (by simp)
    have hc := hS c (by simp)
    rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
      Finset.prod_singleton, Finset.prod_insert (by simp [hab, hac]),
      Finset.prod_insert (by simp [hbc]), Finset.prod_singleton]
    calc a * (b * c) = a * b * c := by ring
      _ ≤ 4 * ((a - 1) * (b - 1) * (c - 1)) := three_bound_sym ha hb hc hab hac hbc
      _ = 4 * ((a - 1) * ((b - 1) * (c - 1))) := by ring

/-- A number with at most three distinct prime factors is not `4`-abundant. -/
lemma sigma_lt_four_mul {n : ℕ} (hn : 1 < n) (hcard : n.primeFactors.card ≤ 3) :
    σ 1 n < 4 * n := by
  have hlt := sigma_mul_prod_pred_lt hn
  have hle := prod_le_four_mul_prod_pred
    (S := n.primeFactors) (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos ?_
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have : σ 1 n * ∏ p ∈ n.primeFactors, (p - 1)
      < (4 * n) * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc σ 1 n * ∏ p ∈ n.primeFactors, (p - 1)
        < n * ∏ p ∈ n.primeFactors, p := hlt
      _ ≤ n * (4 * ∏ p ∈ n.primeFactors, (p - 1)) := Nat.mul_le_mul_left _ hle
      _ = (4 * n) * ∏ p ∈ n.primeFactors, (p - 1) := by ring
  exact Nat.lt_of_mul_lt_mul_right this

/-- **Hagis–Lord, Proposition 2.** If `m` and `n` are coprime betrothed numbers, then
`m * n` has at least four distinct prime factors. -/
theorem coprime_pair_four_primeFactors {m n : ℕ} (h : IsBetrothedPair m n)
    (hcop : Nat.Coprime m n) : 4 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  by_contra hcon
  push_neg at hcon
  have hcard : (m * n).primeFactors.card ≤ 3 := by omega
  have hsigma : σ 1 (m * n) = (m + n + 1) * (m + n + 1) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsm, hsn]
  have hgt : 4 * (m * n) < (m + n + 1) * (m + n + 1) := by
    zify
    nlinarith [sq_nonneg ((m : ℤ) - (n : ℤ))]
  have hmn1 : 1 < m * n := by
    have hpos : 0 < m * n := Nat.mul_pos hm hn
    have hne : m * n ≠ 1 := by
      intro he
      have hm1 : m = 1 := Nat.eq_one_of_mul_eq_one_right he
      have hn1 : n = 1 := Nat.eq_one_of_mul_eq_one_left he
      subst hm1; subst hn1
      rw [ArithmeticFunction.sigma_one] at hsm
      omega
    omega
  have := sigma_lt_four_mul hmn1 hcard
  omega

end BetrothedNumbers

end Brockian

