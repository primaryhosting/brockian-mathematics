import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-! ## The definition -/

/-- A *betrothed* (quasi-amicable) pair: two positive integers each of whose sum of
divisors equals the sum of the two numbers plus one, i.e. `σ₁(m) = σ₁(n) = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- The rational abundancy bound `∏_{p ∣ n} p/(p-1)`, an upper bound for `σ₁(n)/n`. -/
noncomputable def abundancyBound (n : ℕ) : ℚ :=
  ∏ p ∈ n.primeFactors, (p : ℚ) / (p - 1)

/-! ## Parity of the sum of divisors -/

/-- A product of naturals is odd iff each factor is. -/
lemma odd_prod_iff (s : Finset ℕ) (f : ℕ → ℕ) :
    Odd (∏ i ∈ s, f i) ↔ ∀ i ∈ s, Odd (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.prod_insert ha, Nat.odd_mul, ih]

/-- A nonzero natural number is a square iff every exponent in its factorization is even. -/
lemma isSquare_iff_factorization_even {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩ p
    have hr : r ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul hr hr]
    simp [parity_simps]
  · intro h
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add]
    congr 1
    obtain ⟨k, hk⟩ := h p
    omega

/-- For an odd prime `p`, the geometric sum `1 + p + ⋯ + p^e` is odd iff `e` is even. -/
lemma odd_geom_sum_iff {p : ℕ} (hp : Odd p) (e : ℕ) :
    Odd (∑ i ∈ Finset.range (e + 1), p ^ i) ↔ Even e := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Finset.sum_range_succ]
      have hpo : Odd (p ^ (e + 1)) := hp.pow
      rw [Nat.odd_add, Nat.even_add_one]
      simp only [Nat.odd_iff, Nat.even_iff] at *
      omega

/-- **`odd_sigma_one_iff`.**  For an odd positive `n`, the sum of divisors `σ₁(n)` is odd
iff `n` is a perfect square. -/
lemma odd_sigma_one_iff {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) :
    Odd (sigma 1 n) ↔ IsSquare n := by
  have hfac : sigma 1 n
      = ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
    rw [sigma_one_apply, Nat.sum_divisors hn]
  have hodd_p : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd' with h2 | h2
    · exact absurd (Nat.dvd_of_mem_primeFactors hp) (by
        subst h2
        simpa [Nat.odd_iff, Nat.dvd_iff_mod_eq_zero] using hodd)
    · exact h2
  rw [hfac, odd_prod_iff, isSquare_iff_factorization_even hn]
  constructor
  · intro h p
    by_cases hp : p ∈ n.primeFactors
    · exact (odd_geom_sum_iff (hodd_p p hp) _).mp (h p hp)
    · rw [← Nat.support_factorization] at hp
      simp [Finsupp.notMem_support_iff.mp hp]
  · intro h p hp
    exact (odd_geom_sum_iff (hodd_p p hp) _).mpr (h p)

/-! ## The abundancy bound -/

/-- Termwise estimate `1 + p + ⋯ + p^e ≤ p^e · p/(p-1)`. -/
lemma geom_sum_le_pow_mul {p : ℕ} (hp : 2 ≤ p) (e : ℕ) :
    (∑ i ∈ Finset.range (e + 1), (p : ℚ) ^ i) ≤ (p : ℚ) ^ e * ((p : ℚ) / ((p : ℚ) - 1)) := by
  have hx : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have h1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  rw [mul_div_assoc', le_div_iff₀ h1, geom_sum_mul]
  have hpos : (0 : ℚ) < (p : ℚ) ^ (e + 1) := by positivity
  rw [pow_succ] at *
  linarith

/-- `σ₁(n) ≤ n · ∏_{p ∣ n} p/(p-1)`. -/
lemma sigma_one_le_mul_abundancyBound {n : ℕ} (hn : n ≠ 0) :
    (sigma 1 n : ℚ) ≤ n * abundancyBound n := by
  have hcast : ((sigma 1 n : ℕ) : ℚ)
      = ∏ p ∈ n.primeFactors, (∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i) := by
    rw [sigma_one_apply, Nat.sum_divisors hn]
    push_cast
    ring
  have hself : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    ring
  rw [hcast, abundancyBound, hself, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p _ => ?_) (fun p hp => ?_)
  · positivity
  · exact geom_sum_le_pow_mul (Nat.prime_of_mem_primeFactors hp).two_le _

/-- The abundancy bound is multiplicative on coprime arguments. -/
lemma abundancyBound_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : Nat.Coprime m n) :
    abundancyBound (m * n) = abundancyBound m * abundancyBound n := by
  rw [abundancyBound, abundancyBound, abundancyBound, Nat.primeFactors_mul hm hn,
    Finset.prod_union h.disjoint_primeFactors]

/-! ## The numerical bound: twenty odd primes are not enough -/

/-- The twenty smallest odd primes, i.e. all odd primes below `79`. -/
def smallOddPrimes : Finset ℕ :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73}

/-- The product `∏ p/(p-1)` over the twenty smallest odd primes is `< 4`
(its value is `20364840299624512075310661735 / 5133855159158901099724800000 ≈ 3.9668`). -/
lemma prod_smallOddPrimes_lt_four :
    ∏ p ∈ smallOddPrimes, (p : ℚ) / (p - 1) < 4 := by
  have hN : ∏ p ∈ smallOddPrimes, p = 20364840299624512075310661735 := by decide
  have hD : ∏ p ∈ smallOddPrimes, (p - 1) = 5133855159158901099724800000 := by decide
  have hone : ∀ p ∈ smallOddPrimes, 1 ≤ p := by decide
  have key : ∏ p ∈ smallOddPrimes, (p : ℚ) / (p - 1)
      = ((∏ p ∈ smallOddPrimes, p : ℕ) : ℚ) / ((∏ p ∈ smallOddPrimes, (p - 1) : ℕ) : ℚ) := by
    rw [Finset.prod_div_distrib, Nat.cast_prod, Nat.cast_prod]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have h1 := hone p hp
    push_cast [Nat.cast_sub h1]
    ring
  rw [key, hN, hD]
  norm_num

/-- Any set of at most twenty odd primes has `∏ p/(p-1) < 4`. -/
lemma prod_lt_four_of_card_le_twenty {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hcard : S.card ≤ 20) :
    ∏ p ∈ S, (p : ℚ) / (p - 1) < 4 := by
  classical
  set A := smallOddPrimes with hA
  set f : ℕ → ℚ := fun p => (p : ℚ) / (p - 1) with hf
  set T := S.filter (fun p => p ≤ 73) with hT
  set U := S.filter (fun p => ¬ p ≤ 73) with hU
  have hfpos : ∀ p : ℕ, 2 ≤ p → 0 < f p := by
    intro p hp
    have h2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    exact div_pos (by linarith) (by linarith)
  have hTA : T ⊆ A := by
    intro p hp
    rw [hT, Finset.mem_filter] at hp
    obtain ⟨hpS, hple⟩ := hp
    obtain ⟨hpp, hp2⟩ := hS p hpS
    have hall : ∀ q ∈ Finset.range 74, Nat.Prime q → q ≠ 2 → q ∈ smallOddPrimes := by decide
    exact hall p (Finset.mem_range.mpr (by omega)) hpp hp2
  have hTnonneg : 0 ≤ ∏ p ∈ T, f p := by
    refine Finset.prod_nonneg fun p hp => ?_
    rw [hT, Finset.mem_filter] at hp
    exact le_of_lt (hfpos p (hS p hp.1).1.two_le)
  have hUbound : ∏ p ∈ U, f p ≤ (74 / 73 : ℚ) ^ U.card := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · rw [hU, Finset.mem_filter] at hp
      exact le_of_lt (hfpos p (hS p hp.1).1.two_le)
    · rw [hU, Finset.mem_filter] at hp
      have hp74 : (74 : ℚ) ≤ (p : ℚ) := by exact_mod_cast (by omega : 74 ≤ p)
      show (p : ℚ) / (p - 1) ≤ 74 / 73
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
  have hAdiff : (73 / 72 : ℚ) ^ ((A \ T).card) ≤ ∏ p ∈ A \ T, f p := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun p _ => by norm_num) (fun p hp => ?_)
    have hpA : p ∈ A := (Finset.mem_sdiff.mp hp).1
    have hb : ∀ q ∈ smallOddPrimes, 3 ≤ q ∧ q ≤ 73 := by decide
    obtain ⟨h3, h73⟩ := hb p hpA
    have h3' : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
    have h73' : (p : ℚ) ≤ 73 := by exact_mod_cast h73
    show (73 / 72 : ℚ) ≤ (p : ℚ) / (p - 1)
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  have hcards : U.card ≤ (A \ T).card := by
    have h1 : (A \ T).card = A.card - T.card := Finset.card_sdiff_of_subset hTA
    have h2 : A.card = 20 := by decide
    have h3 : T.card + U.card = S.card := Finset.card_filter_add_card_filter_not _
    have h4 : T.card ≤ A.card := Finset.card_le_card hTA
    omega
  have hpow : (74 / 73 : ℚ) ^ U.card ≤ (73 / 72 : ℚ) ^ ((A \ T).card) :=
    calc (74 / 73 : ℚ) ^ U.card ≤ (73 / 72 : ℚ) ^ U.card :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ ≤ (73 / 72 : ℚ) ^ ((A \ T).card) := pow_le_pow_right₀ (by norm_num) hcards
  calc ∏ p ∈ S, f p = (∏ p ∈ T, f p) * ∏ p ∈ U, f p :=
        (Finset.prod_filter_mul_prod_filter_not S _ f).symm
    _ ≤ (∏ p ∈ T, f p) * (74 / 73 : ℚ) ^ U.card := mul_le_mul_of_nonneg_left hUbound hTnonneg
    _ ≤ (∏ p ∈ T, f p) * (73 / 72 : ℚ) ^ ((A \ T).card) :=
        mul_le_mul_of_nonneg_left hpow hTnonneg
    _ ≤ (∏ p ∈ T, f p) * ∏ p ∈ A \ T, f p := mul_le_mul_of_nonneg_left hAdiff hTnonneg
    _ = ∏ p ∈ A, f p := by rw [mul_comm]; exact Finset.prod_sdiff hTA
    _ < 4 := prod_smallOddPrimes_lt_four

/-! ## The abundancy of a coprime betrothed pair -/

/-- For a coprime betrothed pair the abundancy bound of the product exceeds `4`. -/
lemma four_lt_abundancyBound_mul {m n : ℕ} (h : IsBetrothedPair m n)
    (hcop : Nat.Coprime m n) : 4 < abundancyBound (m * n) := by
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  have hm0 : m ≠ 0 := hm.ne'
  have hn0 : n ≠ 0 := hn.ne'
  have hmQ : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hnQ : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have h1 : ((m : ℚ) + n + 1) ≤ m * abundancyBound m := by
    have := sigma_one_le_mul_abundancyBound hm0
    rw [hsm] at this
    push_cast at this
    linarith
  have h2 : ((m : ℚ) + n + 1) ≤ n * abundancyBound n := by
    have := sigma_one_le_mul_abundancyBound hn0
    rw [hsn] at this
    push_cast at this
    linarith
  have hprod : ((m : ℚ) + n + 1) ^ 2 ≤ (m * n) * (abundancyBound m * abundancyBound n) := by
    have hpos : (0 : ℚ) ≤ (m : ℚ) + n + 1 := by linarith
    calc ((m : ℚ) + n + 1) ^ 2 = ((m : ℚ) + n + 1) * ((m : ℚ) + n + 1) := by ring
      _ ≤ ((m : ℚ) * abundancyBound m) * ((n : ℚ) * abundancyBound n) := by
          exact mul_le_mul h1 h2 hpos (le_trans hpos h1)
      _ = (m * n) * (abundancyBound m * abundancyBound n) := by ring
  have hgt : 4 * ((m : ℚ) * n) < ((m : ℚ) + n + 1) ^ 2 := by nlinarith [sq_nonneg ((m : ℚ) - n)]
  have hmn : (0 : ℚ) < (m : ℚ) * n := by positivity
  rw [abundancyBound_mul_of_coprime hm0 hn0 hcop]
  have : 4 * ((m : ℚ) * n) < ((m : ℚ) * n) * (abundancyBound m * abundancyBound n) := by
    linarith
  nlinarith [this]

/-! ## The main theorem -/

/-- **Hagis–Lord, Proposition 2 (second part).**  If `(m, n)` is a betrothed
(quasi-amicable) pair with `gcd(m, n) = 1` whose two members have the same parity, then
both members are odd and the product `m * n` has at least twenty-one distinct prime
factors.

This is the exact, unconditional statement.  It should be distinguished from the
*historical computational lower bounds* for betrothed pairs (searches by Hagis and Lord
and later authors show that no coprime betrothed pair exists below various computational
search limits, and give much larger numerical bounds); no such computational claim is
asserted or used here. -/
theorem coprime_sameParity_twentyOne_primeFactors {m n : ℕ}
    (h : IsBetrothedPair m n) (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    Odd m ∧ Odd n ∧ 21 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  -- both members are odd, since two even numbers cannot be coprime
  have hmodd : m % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · exfalso
      have hn0 : n % 2 = 0 := by omega
      have h2m : 2 ∣ m := Nat.dvd_of_mod_eq_zero h0
      have h2n : 2 ∣ n := Nat.dvd_of_mod_eq_zero hn0
      have : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd h2m h2n
      rw [hcop] at this
      omega
    · exact h1
  have hnodd : n % 2 = 1 := by omega
  refine ⟨Nat.odd_iff.mpr hmodd, Nat.odd_iff.mpr hnodd, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hcard : (m * n).primeFactors.card ≤ 20 := by omega
  have hmnodd : (m * n) % 2 = 1 := by
    rw [Nat.mul_mod, hmodd, hnodd]
  have hS : ∀ p ∈ (m * n).primeFactors, p.Prime ∧ p ≠ 2 := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    rintro rfl
    have hdvd : 2 ∣ m * n := Nat.dvd_of_mem_primeFactors hp
    omega
  have hlt : abundancyBound (m * n) < 4 := prod_lt_four_of_card_le_twenty hS hcard
  have hgt : 4 < abundancyBound (m * n) :=
    four_lt_abundancyBound_mul ⟨hm, hn, hsm, hsn⟩ hcop
  linarith

/-- Complementary part of Hagis–Lord, Proposition 2: the two members of a coprime
same-parity betrothed pair are perfect squares (they are odd with odd sum of divisors). -/
theorem coprime_sameParity_isSquare {m n : ℕ}
    (h : IsBetrothedPair m n) (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    IsSquare m ∧ IsSquare n := by
  obtain ⟨hmodd, hnodd, -⟩ := coprime_sameParity_twentyOne_primeFactors h hcop hpar
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  have hsum : Odd (m + n + 1) := by
    rw [Nat.odd_iff] at *
    omega
  refine ⟨(odd_sigma_one_iff hm.ne' hmodd).mp ?_, (odd_sigma_one_iff hn.ne' hnodd).mp ?_⟩
  · rw [hsm]; exact hsum
  · rw [hsn]; exact hsum

/-- Sanity check: betrothed pairs do exist, e.g. `(48, 75)`; this pair is coprime but its
members have different parities, so it is not covered by the theorem above.  Indeed no
coprime same-parity betrothed pair is known: the historical computational searches
(Hagis–Lord and later authors) have found none, but those are *computational* results and
are deliberately not asserted here. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> decide

end Brockian.BetrothedNumbers

