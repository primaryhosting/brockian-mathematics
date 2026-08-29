import Mathlib

/-!
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Finset

namespace CS

/-- For `q` a prime factor of `n` with `q < n`, the product `∏_{i=1}^{q-1} (n - i)`
is not divisible by `q`. -/
lemma not_dvd_prod_Ico {n q : ℕ} (hq : q.Prime) (hqn : q ∣ n) (hlt : q < n) :
    ¬ q ∣ ∏ i ∈ Finset.Ico 1 q, (n - i) := by
  intro h
  obtain ⟨i, hi, hdvd⟩ := hq.prime.exists_mem_finset_dvd h
  simp only [Finset.mem_Ico] at hi
  have hin : i < n := lt_trans hi.2 hlt
  have hqi : q ∣ i := by
    have h' : i = n - (n - i) := by omega
    rw [h']
    exact Nat.dvd_sub hqn hdvd
  have := Nat.le_of_dvd (by omega) hqi
  omega

/-- The `q`-adic valuation of `n.choose q` is one less than that of `n`,
when `q` is a prime factor of `n` with `q < n`. -/
lemma factorization_choose_of_prime_dvd {n q : ℕ} (hq : q.Prime) (hqn : q ∣ n) (hlt : q < n) :
    (n.choose q).factorization q + 1 = n.factorization q := by
  have hn0 : n ≠ 0 := by omega
  have hq2 : 2 ≤ q := hq.two_le
  set M := ∏ i ∈ Finset.Ico 1 q, (n - i) with hM
  have hM0 : M ≠ 0 := by
    rw [hM, Finset.prod_ne_zero_iff]
    intro i hi
    simp only [Finset.mem_Ico] at hi
    omega
  have hqM : ¬ q ∣ M := not_dvd_prod_Ico hq hqn hlt
  have hdesc : n.descFactorial q = n * M := by
    rw [Nat.descFactorial_eq_prod_range, Finset.range_eq_Ico,
      Finset.prod_eq_prod_Ico_succ_bot hq.pos]
    simp [hM]
  have hkey : q.factorial * n.choose q = n * M := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, hdesc]
  have hc0 : n.choose q ≠ 0 := (Nat.choose_pos (le_of_lt hlt)).ne'
  have hfac0 : q.factorial ≠ 0 := Nat.factorial_ne_zero q
  -- valuation of `q !` at `q` is one
  have hfacq : (q.factorial).factorization q = 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    rw [Nat.factorial_succ, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero m)]
    have : ¬ (m + 1) ∣ m.factorial := by
      intro h
      have := (Nat.Prime.dvd_factorial hq).mp h
      omega
    simp [hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd this]
  have h1 : (q.factorial * n.choose q).factorization q
      = 1 + (n.choose q).factorization q := by
    rw [Nat.factorization_mul hfac0 hc0]
    simp [hfacq]
  have h2 : (n * M).factorization q = n.factorization q := by
    rw [Nat.factorization_mul hn0 hM0]
    simp [Nat.factorization_eq_zero_of_not_dvd hqM]
  rw [hkey, h2] at h1
  omega

/-- If `n ≥ 2` is not prime, the polynomial congruence `(X+1)^n = X^n + 1` fails
in `(ZMod n)[X]`. -/
lemma not_congr_of_not_prime {n : ℕ} (hn : 2 ≤ n) (hnp : ¬ n.Prime) :
    ((X + 1 : (ZMod n)[X]))^n ≠ X^n + 1 := by
  intro heq
  set q := n.minFac with hqdef
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqn : q ∣ n := Nat.minFac_dvd n
  have hlt : q < n := by
    rcases lt_or_eq_of_le (Nat.minFac_le (by omega : 0 < n)) with h | h
    · exact h
    · exact absurd (h ▸ hq) hnp
  -- compare coefficients of `X ^ q`
  have hcoeff := congrArg (fun p => Polynomial.coeff p q) heq
  simp only [Polynomial.coeff_X_add_one_pow, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_one, if_neg (by omega : ¬ q = n), if_neg (by have := hq.two_le; omega : ¬ q = 0)]
    at hcoeff
  have hdvd : n ∣ n.choose q := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hcoeff)
  have hc0 : n.choose q ≠ 0 := (Nat.choose_pos (le_of_lt hlt)).ne'
  have hfc := factorization_choose_of_prime_dvd hq hqn hlt
  have hpow : q ^ (n.factorization q) ∣ n.choose q :=
    dvd_trans (Nat.ordProj_dvd n q) hdvd
  have := (Nat.Prime.pow_dvd_iff_le_factorization hq hc0).mp hpow
  omega

/-- **AKS criterion (Agrawal–Kayal–Saxena).**  For `n ≥ 2`, the number `n` is prime if and
only if the polynomial identity `(X + a)^n = X^n + a^n` holds in `(ZMod n)[X]` for every
`a` coprime to `n`.

This is the algebraic characterization of primality on which the AKS deterministic
polynomial-time primality test ("PRIMES is in P") is based.  Note that what is formalized
here is this mathematical criterion, not the complexity-theoretic assertion about a machine
model (Mathlib provides no time-complexity framework in which the latter could be stated). -/
theorem aks_primes_in_p (n : ℕ) (hn : 2 ≤ n) :
    n.Prime ↔ ∀ a : ℕ, Nat.Coprime a n →
      (X + C (a : ZMod n)) ^ n = X ^ n + C ((a : ZMod n) ^ n) := by
  constructor
  · intro hp a _
    haveI : Fact n.Prime := ⟨hp⟩
    rw [add_pow_char, ← map_pow]
  · intro h
    by_contra hnp
    refine not_congr_of_not_prime hn hnp ?_
    have := h 1 (Nat.coprime_one_left n)
    simpa using this

/-- The classical special case of the AKS criterion: for `n ≥ 2`, `n` is prime if and only if
`(X + 1) ^ n = X ^ n + 1` in `(ZMod n)[X]`. -/
theorem prime_iff_X_add_one_pow (n : ℕ) (hn : 2 ≤ n) :
    n.Prime ↔ ((X + 1 : (ZMod n)[X])) ^ n = X ^ n + 1 := by
  refine ⟨fun hp => ?_, fun h => by_contra fun hnp => not_congr_of_not_prime hn hnp h⟩
  have := (aks_primes_in_p n hn).mp hp 1 (Nat.coprime_one_left n)
  simpa using this

end CS

#print axioms CS.aks_primes_in_p
#print axioms CS.prime_iff_X_add_one_pow

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

