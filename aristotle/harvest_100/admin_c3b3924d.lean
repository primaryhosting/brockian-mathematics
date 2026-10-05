import Mathlib
/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose
divisor sums equals the sum of the pair plus one. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- Sanity check: `(48, 75)` is the smallest betrothed pair.  (Its members are
coprime but of *opposite* parity, so it is not covered by the theorem below.) -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> · rw [sigma_one_apply]; rfl

/-! ## The abundancy bound `σ(N)/N ≤ ∏_{p ∣ N} p/(p-1)` -/

/-- The factor `p/(p-1)`, as a rational number. -/
noncomputable def abFactor (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

lemma one_le_abFactor {a : ℕ} (ha : 2 ≤ a) : 1 ≤ abFactor a := by
  have h : (2:ℚ) ≤ (a:ℚ) := by exact_mod_cast ha
  rw [abFactor, le_div_iff₀ (by linarith)]
  linarith

lemma abFactor_nonneg {a : ℕ} (ha : 2 ≤ a) : (0:ℚ) ≤ abFactor a :=
  le_trans zero_le_one (one_le_abFactor ha)

lemma abFactor_antitone {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    abFactor b ≤ abFactor a := by
  have h : (2:ℚ) ≤ (a:ℚ) := by exact_mod_cast ha
  have h2 : (a:ℚ) ≤ (b:ℚ) := by exact_mod_cast hab
  rw [abFactor, abFactor, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- For a prime power, `σ(p^a) ≤ p^a · p/(p-1)`. -/
lemma sigma_primePow_le {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ((sigma 1 (p ^ a) : ℕ) : ℚ) ≤ (p : ℚ) ^ a * abFactor p := by
  have hp2 : (2:ℚ) ≤ (p:ℚ) := by exact_mod_cast hp.two_le
  have hs : (sigma 1) (p ^ a) = ∑ i ∈ Finset.range (a + 1), p ^ i := by
    rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  have key : (∑ i ∈ Finset.range (a + 1), (p:ℚ) ^ i) * ((p:ℚ) - 1) = (p:ℚ) ^ (a + 1) - 1 :=
    geom_sum_mul _ _
  rw [pow_succ] at key
  rw [hs]
  push_cast
  rw [abFactor, mul_div_assoc', le_div_iff₀ (by linarith)]
  linarith [key]

/-- The rational abundancy bound: `σ(N) ≤ N · ∏_{p ∣ N} p/(p-1)`. -/
lemma sigma_le_prod_abFactor {N : ℕ} (hN : N ≠ 0) :
    ((sigma 1 N : ℕ) : ℚ) ≤ (N : ℚ) * ∏ p ∈ N.primeFactors, abFactor p := by
  have h1 : (sigma 1) N = ∏ p ∈ N.primeFactors, (sigma 1) (p ^ N.factorization p) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hN]
    rfl
  have h2 : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rfl
  rw [h1]
  push_cast
  calc ∏ p ∈ N.primeFactors, ((sigma 1) (p ^ N.factorization p) : ℚ)
      ≤ ∏ p ∈ N.primeFactors, ((p:ℚ) ^ N.factorization p * abFactor p) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro i _; positivity
        · intro i hi
          exact_mod_cast sigma_primePow_le (Nat.prime_of_mem_primeFactors hi) _
    _ = (N : ℚ) * ∏ p ∈ N.primeFactors, abFactor p := by
        rw [Finset.prod_mul_distrib]
        congr 1
        conv_rhs => rw [h2]
        push_cast
        ring

/-! ## The product of `p/(p-1)` over at most twenty odd primes is less than four -/

lemma nth_prime_eq {q k : ℕ} (hq : q.Prime) (hk : Nat.count Nat.Prime q = k) :
    Nat.nth Nat.Prime k = q := hk ▸ Nat.nth_count hq

/-- The running bound: the product of `p/(p-1)` over the first `k` *odd* primes
(the primes `Nat.nth Nat.Prime 1, …, Nat.nth Nat.Prime k`, i.e. `3, 5, 7, …`). -/
noncomputable def oddPrimeBound (k : ℕ) : ℚ :=
  ∏ i ∈ Finset.range k, abFactor (Nat.nth Nat.Prime (i + 1))

lemma one_le_oddPrimeBound (k : ℕ) : 1 ≤ oddPrimeBound k :=
  Finset.one_le_prod _ (fun _ => one_le_abFactor (Nat.prime_nth_prime _).two_le)

lemma oddPrimeBound_succ (k : ℕ) :
    oddPrimeBound (k + 1) = oddPrimeBound k * abFactor (Nat.nth Nat.Prime (k + 1)) := by
  rw [oddPrimeBound, oddPrimeBound, Finset.prod_range_succ]

lemma oddPrimeBound_mono {j k : ℕ} (hjk : j ≤ k) : oddPrimeBound j ≤ oddPrimeBound k := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_refl _
  | succ k _ ih =>
      refine ih.trans ?_
      rw [oddPrimeBound_succ]
      nlinarith [one_le_oddPrimeBound k, one_le_abFactor (Nat.prime_nth_prime (k + 1)).two_le]

/-- A nonempty finite set of `k` odd primes, all at most `m`, forces `m` to be at
least the `k`-th odd prime `Nat.nth Nat.Prime k`. -/
lemma max_ge_nth_prime {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime) (h3 : ∀ p ∈ S, 3 ≤ p)
    {m : ℕ} (hm : ∀ p ∈ S, p ≤ m) (hne : S.Nonempty) : Nat.nth Nat.Prime S.card ≤ m := by
  obtain ⟨x, hx⟩ := hne
  have hm2 : 2 ≤ m := le_trans (h3 x hx) (hm x hx) |>.trans' (by omega)
  by_contra hcon
  push_neg at hcon
  have h2S : (2:ℕ) ∉ S := fun h => by have := h3 2 h; omega
  have hsub : insert 2 S ⊆ (Finset.range (m + 1)).filter Nat.Prime := by
    intro y hy
    simp only [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Nat.prime_two⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by have := hm y hy; omega, hp y hy⟩
  have hcard : S.card + 1 ≤ Nat.count Nat.Prime (m + 1) := by
    rw [Nat.count_eq_card_filter_range]
    have := Finset.card_le_card hsub
    rwa [Finset.card_insert_of_notMem h2S] at this
  have hmono : Nat.count Nat.Prime (m + 1) ≤ Nat.count Nat.Prime (Nat.nth Nat.Prime S.card) :=
    Nat.count_monotone _ (by omega)
  rw [Nat.count_nth_of_infinite Nat.infinite_setOf_prime] at hmono
  omega

lemma prod_abFactor_le_bound : ∀ (n : ℕ) (S : Finset ℕ), S.card = n → (∀ p ∈ S, p.Prime) →
    (∀ p ∈ S, 3 ≤ p) → ∏ p ∈ S, abFactor p ≤ oddPrimeBound n := by
  intro n
  induction n with
  | zero =>
      intro S hS _ _
      rw [Finset.card_eq_zero] at hS
      subst hS
      simp [oddPrimeBound]
  | succ n ih =>
      intro S hS hp h3
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      set m := S.max' hne with hmdef
      have hmS : m ∈ S := S.max'_mem hne
      have hle : ∀ p ∈ S, p ≤ m := fun p hp' => S.le_max' p hp'
      have hnth : Nat.nth Nat.Prime (n + 1) ≤ m := by
        have := max_ge_nth_prime hp h3 hle hne
        rwa [hS] at this
      have hprod : ∏ p ∈ S, abFactor p = abFactor m * ∏ p ∈ S.erase m, abFactor p :=
        (Finset.mul_prod_erase _ _ hmS).symm
      have hcarderase : (S.erase m).card = n := by
        rw [Finset.card_erase_of_mem hmS, hS]
        omega
      have hih := ih (S.erase m) hcarderase (fun p hp' => hp p (Finset.mem_of_mem_erase hp'))
        (fun p hp' => h3 p (Finset.mem_of_mem_erase hp'))
      have h1 : abFactor m ≤ abFactor (Nat.nth Nat.Prime (n + 1)) :=
        abFactor_antitone (Nat.prime_nth_prime _).two_le hnth
      have h2 : (0:ℚ) ≤ abFactor m := abFactor_nonneg (by have := h3 m hmS; omega)
      have h4 : (0:ℚ) ≤ ∏ p ∈ S.erase m, abFactor p :=
        Finset.prod_nonneg (fun p hp' =>
          abFactor_nonneg (by have := h3 p (Finset.mem_of_mem_erase hp'); omega))
      rw [hprod, oddPrimeBound_succ]
      calc abFactor m * ∏ p ∈ S.erase m, abFactor p
          ≤ abFactor (Nat.nth Nat.Prime (n + 1)) * oddPrimeBound n :=
            mul_le_mul h1 hih h4 (le_trans h2 h1)
        _ = oddPrimeBound n * abFactor (Nat.nth Nat.Prime (n + 1)) := mul_comm _ _

lemma oddPrimeBound_twenty_lt_four : oddPrimeBound 20 < 4 := by
  have e1 : Nat.nth Nat.Prime 1 = 3 := nth_prime_eq (by norm_num) (by decide)
  have e2 : Nat.nth Nat.Prime 2 = 5 := nth_prime_eq (by norm_num) (by decide)
  have e3 : Nat.nth Nat.Prime 3 = 7 := nth_prime_eq (by norm_num) (by decide)
  have e4 : Nat.nth Nat.Prime 4 = 11 := nth_prime_eq (by norm_num) (by decide)
  have e5 : Nat.nth Nat.Prime 5 = 13 := nth_prime_eq (by norm_num) (by decide)
  have e6 : Nat.nth Nat.Prime 6 = 17 := nth_prime_eq (by norm_num) (by decide)
  have e7 : Nat.nth Nat.Prime 7 = 19 := nth_prime_eq (by norm_num) (by decide)
  have e8 : Nat.nth Nat.Prime 8 = 23 := nth_prime_eq (by norm_num) (by decide)
  have e9 : Nat.nth Nat.Prime 9 = 29 := nth_prime_eq (by norm_num) (by decide)
  have e10 : Nat.nth Nat.Prime 10 = 31 := nth_prime_eq (by norm_num) (by decide)
  have e11 : Nat.nth Nat.Prime 11 = 37 := nth_prime_eq (by norm_num) (by decide)
  have e12 : Nat.nth Nat.Prime 12 = 41 := nth_prime_eq (by norm_num) (by decide)
  have e13 : Nat.nth Nat.Prime 13 = 43 := nth_prime_eq (by norm_num) (by decide)
  have e14 : Nat.nth Nat.Prime 14 = 47 := nth_prime_eq (by norm_num) (by decide)
  have e15 : Nat.nth Nat.Prime 15 = 53 := nth_prime_eq (by norm_num) (by decide)
  have e16 : Nat.nth Nat.Prime 16 = 59 := nth_prime_eq (by norm_num) (by decide)
  have e17 : Nat.nth Nat.Prime 17 = 61 := nth_prime_eq (by norm_num) (by decide)
  have e18 : Nat.nth Nat.Prime 18 = 67 := nth_prime_eq (by norm_num) (by decide)
  have e19 : Nat.nth Nat.Prime 19 = 71 := nth_prime_eq (by norm_num) (by decide)
  have e20 : Nat.nth Nat.Prime 20 = 73 := nth_prime_eq (by norm_num) (by decide)
  rw [oddPrimeBound]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero,
    show (0:ℕ) + 1 = 1 from rfl, show (1:ℕ) + 1 = 2 from rfl, show (2:ℕ) + 1 = 3 from rfl,
    show (3:ℕ) + 1 = 4 from rfl, show (4:ℕ) + 1 = 5 from rfl, show (5:ℕ) + 1 = 6 from rfl,
    show (6:ℕ) + 1 = 7 from rfl, show (7:ℕ) + 1 = 8 from rfl, show (8:ℕ) + 1 = 9 from rfl,
    show (9:ℕ) + 1 = 10 from rfl, show (10:ℕ) + 1 = 11 from rfl, show (11:ℕ) + 1 = 12 from rfl,
    show (12:ℕ) + 1 = 13 from rfl, show (13:ℕ) + 1 = 14 from rfl, show (14:ℕ) + 1 = 15 from rfl,
    show (15:ℕ) + 1 = 16 from rfl, show (16:ℕ) + 1 = 17 from rfl, show (17:ℕ) + 1 = 18 from rfl,
    show (18:ℕ) + 1 = 19 from rfl, show (19:ℕ) + 1 = 20 from rfl,
    e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20,
    abFactor]
  norm_num

lemma prod_abFactor_lt_four (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime) (h3 : ∀ p ∈ S, 3 ≤ p)
    (hcard : S.card ≤ 20) : ∏ p ∈ S, abFactor p < 4 :=
  lt_of_le_of_lt ((prod_abFactor_le_bound S.card S rfl hp h3).trans
    (oddPrimeBound_mono hcard)) oddPrimeBound_twenty_lt_four

/-! ## Odd `4`-abundant numbers have at least twenty-one prime factors -/

lemma odd_of_mem_primeFactors {N p : ℕ} (hodd : Odd N) (hp : p ∈ N.primeFactors) : Odd p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  refine hpp.odd_of_ne_two ?_
  rintro rfl
  obtain ⟨c, rfl⟩ := hdvd
  have := Nat.odd_iff.mp hodd
  omega

lemma card_primeFactors_ge_of_odd_abundant {N : ℕ} (hN : N ≠ 0) (hodd : Odd N)
    (habund : 4 * N ≤ sigma 1 N) : 21 ≤ N.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hcard : N.primeFactors.card ≤ 20 := by omega
  have hp : ∀ p ∈ N.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h3 : ∀ p ∈ N.primeFactors, 3 ≤ p := by
    intro p hpm
    have hpp := Nat.prime_of_mem_primeFactors hpm
    have hp2 := hpp.two_le
    have := Nat.odd_iff.mp (odd_of_mem_primeFactors hodd hpm)
    omega
  have hlt := prod_abFactor_lt_four N.primeFactors hp h3 hcard
  have hle := sigma_le_prod_abFactor hN
  have hNpos : (0:ℚ) < (N:ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hab : (4:ℚ) * (N:ℚ) ≤ ((sigma 1 N : ℕ) : ℚ) := by exact_mod_cast habund
  nlinarith [hle, hlt, hNpos, hab]

/-! ## Parity of `σ`: `σ(n)` is odd exactly when the odd number `n` is a square -/

lemma geom_sum_mod_two {p : ℕ} (hodd : Odd p) (a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), p ^ i) % 2 = (a + 1) % 2 := by
  have hpow : ∀ i : ℕ, p ^ i % 2 = 1 := fun i => Nat.odd_iff.mp (hodd.pow)
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Finset.sum_range_succ]
      have := hpow (a + 1)
      omega

lemma sigma_primePow_mod_two {p : ℕ} (hp : p.Prime) (hodd : Odd p) (a : ℕ) :
    (sigma 1 (p ^ a)) % 2 = (a + 1) % 2 := by
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  exact geom_sum_mod_two hodd a

lemma isSquare_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, Even (n.factorization p)) : IsSquare n := by
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [← pow_add]
  congr 1
  obtain ⟨c, hc⟩ := h p hp
  omega

/-- For an odd positive integer `n`, the divisor sum `σ(n)` is odd if and only if
`n` is a perfect square. -/
lemma odd_sigma_one_iff {n : ℕ} (hn0 : n ≠ 0) (hodd : Odd n) :
    Odd (sigma 1 n) ↔ IsSquare n := by
  have hprod : sigma 1 n = ∏ p ∈ n.primeFactors, sigma 1 (p ^ n.factorization p) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
    rfl
  constructor
  · intro h
    refine isSquare_of_factorization_even hn0 ?_
    intro p hp
    by_contra hEven
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpo := odd_of_mem_primeFactors hodd hp
    have hmod := sigma_primePow_mod_two hpp hpo (n.factorization p)
    have hdvd2 : 2 ∣ sigma 1 (p ^ n.factorization p) := by
      rw [Nat.even_iff] at hEven
      omega
    have h2 : (2:ℕ) ∣ sigma 1 n := by
      rw [hprod]
      exact hdvd2.trans (Finset.dvd_prod_of_mem _ hp)
    rw [Nat.odd_iff] at h
    omega
  · rintro ⟨k, hk⟩
    rw [Nat.odd_iff, hprod, ← Nat.not_even_iff, even_iff_two_dvd]
    intro hcon
    rw [Nat.prime_two.prime.dvd_finset_prod_iff] at hcon
    obtain ⟨p, hp, hdvd⟩ := hcon
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpo := odd_of_mem_primeFactors hodd hp
    have hmod := sigma_primePow_mod_two hpp hpo (n.factorization p)
    have heven : n.factorization p = 2 * (k.factorization p) := by
      rw [hk, ← sq, Nat.factorization_pow]
      simp
    omega

/-! ## The main theorem -/

/-- **Hagis–Lord, Proposition 2 (second part).**  If `(m, n)` is a betrothed
(quasi-amicable) pair whose members are coprime and of the same parity, then both
members are odd and the product `m * n` has at least twenty-one distinct prime
factors.

This is the exact, unconditional statement.  The much larger *computational*
lower bounds attached to this proposition in the literature (for instance that
such a pair would have to satisfy `m * n > 10 ^ 60`) rest on machine searches and
are deliberately **not** asserted here; only the twenty-one prime factor bound,
which follows from the rational abundancy estimate, is formalized. -/
theorem coprime_sameParity_twentyOne_primeFactors {m n : ℕ}
    (hb : IsBetrothedPair m n) (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    Odd m ∧ Odd n ∧ 21 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm0, hn0, hsm, hsn⟩ := hb
  -- both members are odd, since two even members could not be coprime
  have hmodd : m % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · exfalso
      have hn : n % 2 = 0 := by omega
      have h2m : (2:ℕ) ∣ m := Nat.dvd_of_mod_eq_zero h
      have h2n : (2:ℕ) ∣ n := Nat.dvd_of_mod_eq_zero hn
      have : (2:ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd h2m h2n
      rw [Nat.Coprime] at hcop
      omega
    · exact h
  have hnodd : n % 2 = 1 := by omega
  refine ⟨Nat.odd_iff.mpr hmodd, Nat.odd_iff.mpr hnodd, ?_⟩
  -- the product is odd and `4`-abundant
  have hNodd : Odd (m * n) := (Nat.odd_iff.mpr hmodd).mul (Nat.odd_iff.mpr hnodd)
  have hN : m * n ≠ 0 := by positivity
  have hsigma : sigma 1 (m * n) = (m + n + 1) * (m + n + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, hsm, hsn]
  have habund : 4 * (m * n) ≤ sigma 1 (m * n) := by
    rw [hsigma]
    nlinarith [sq_nonneg ((m : ℤ) - (n : ℤ)), Nat.zero_le m, Nat.zero_le n]
  exact card_primeFactors_ge_of_odd_abundant hN hNodd habund

/-- Companion to the main theorem (the first half of Hagis–Lord, Proposition 2):
both members of a coprime, same-parity betrothed pair are perfect squares. -/
theorem coprime_sameParity_isSquare {m n : ℕ}
    (hb : IsBetrothedPair m n) (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    IsSquare m ∧ IsSquare n := by
  obtain ⟨hmodd, hnodd, -⟩ := coprime_sameParity_twentyOne_primeFactors hb hcop hpar
  obtain ⟨hm0, hn0, hsm, hsn⟩ := hb
  have hsum : Odd (m + n + 1) := by
    have h1 := Nat.odd_iff.mp hmodd
    have h2 := Nat.odd_iff.mp hnodd
    exact Nat.odd_iff.mpr (by omega)
  constructor
  · exact (odd_sigma_one_iff (by omega) hmodd).mp (by rw [hsm]; exact hsum)
  · exact (odd_sigma_one_iff (by omega) hnodd).mp (by rw [hsn]; exact hsum)

/-! ## Historical computational lower bounds (not formalized)

The statement proved above is the exact, unconditional part of Hagis–Lord,
Proposition 2.  The literature additionally records *computational* lower bounds
for a hypothetical coprime same-parity betrothed pair — obtained by exhaustive
machine search rather than by proof from first principles.  Such bounds are
deliberately not asserted anywhere in this file: no axiom, definition or theorem
here depends on them. -/

end Brockian.BetrothedNumbers

