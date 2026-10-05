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

/-
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

open Zsqrtd

/-- A *Landau prime* is a prime natural number of the form `n ^ 2 + 1`. -/
def IsLandauPrime (p : ℕ) : Prop := Nat.Prime p ∧ ∃ n : ℕ, p = n ^ 2 + 1

/-- The set of primes of the form `n ^ 2 + 1`. -/
def landauPrimes : Set ℕ := {p | IsLandauPrime p}

/-- The set of natural numbers `n` for which `n + i` is a Gaussian prime. -/
def gaussianBases : Set ℕ := {n | Prime (⟨(n : ℤ), 1⟩ : GaussianInt)}

/-- Gaussian reformulation of Landau's fourth conjecture: there are infinitely
many Gaussian primes of the form `n + i` with `n` a natural number. -/
def GaussianPrimeFormulation : Prop := gaussianBases.Infinite

/-- Landau's fourth conjecture: there are infinitely many primes of the form `n ^ 2 + 1`. -/
def LandauFourthStatement : Prop := landauPrimes.Infinite

/-! ## Norms of Gaussian integers of the form `n + i` -/

lemma norm_mk_one (n : ℕ) : (⟨(n : ℤ), 1⟩ : GaussianInt).norm = ((n ^ 2 + 1 : ℕ) : ℤ) := by
  simp [Zsqrtd.norm]
  ring

/-- If the absolute value of the norm of a Gaussian integer is a rational prime,
then the Gaussian integer is prime. -/
lemma prime_of_natAbs_norm_prime {x : GaussianInt} (h : Nat.Prime x.norm.natAbs) : Prime x := by
  rw [← irreducible_iff_prime]
  refine ⟨fun hu => h.ne_one (norm_eq_one_iff.2 hu), ?_⟩
  intro a b hab
  have hn : x.norm.natAbs = a.norm.natAbs * b.norm.natAbs := by
    rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul]
  rw [hn] at h
  rcases Nat.prime_mul_iff.1 h with ⟨_, hb⟩ | ⟨_, ha⟩
  · exact Or.inr (norm_eq_one_iff.1 hb)
  · exact Or.inl (norm_eq_one_iff.1 ha)

/-- If `n ^ 2 + 1` is prime, then `n + i` is a Gaussian prime. -/
lemma gaussianPrime_of_prime_sq_add_one {n : ℕ} (h : Nat.Prime (n ^ 2 + 1)) :
    Prime (⟨(n : ℤ), 1⟩ : GaussianInt) := by
  apply prime_of_natAbs_norm_prime
  rw [norm_mk_one]
  simpa using h

/-- A prime Gaussian integer dividing a nonzero natural number divides one of its
rational prime factors. -/
lemma exists_natPrime_dvd_of_dvd_natCast {x : GaussianInt} (hx : Prime x) {m : ℕ} (hm : m ≠ 0)
    (hdvd : x ∣ (m : GaussianInt)) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ m ∧ x ∣ (p : GaussianInt) := by
  have hprod : ((m : GaussianInt)) =
      (m.primeFactorsList.map (fun p : ℕ => (p : GaussianInt))).prod := by
    rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList hm]
  rw [hprod] at hdvd
  obtain ⟨a, ha, hxa⟩ := hx.dvd_prod_iff.1 hdvd
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, Nat.dvd_of_mem_primeFactorsList hp, hxa⟩

/-- If `n + i` is a Gaussian prime, then `n ^ 2 + 1` is a rational prime. -/
lemma prime_sq_add_one_of_gaussianPrime {n : ℕ} (h : Prime (⟨(n : ℤ), 1⟩ : GaussianInt)) :
    Nat.Prime (n ^ 2 + 1) := by
  set x : GaussianInt := ⟨(n : ℤ), 1⟩ with hx
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact h.not_unit (norm_eq_one_iff.1 (by simp [hx, Zsqrtd.norm]))
  have hxdvd : x ∣ ((n ^ 2 + 1 : ℕ) : GaussianInt) := by
    refine ⟨star x, ?_⟩
    have h1 : ((x.norm : ℤ) : GaussianInt) = x * star x := Zsqrtd.norm_eq_mul_conj x
    rw [← h1, hx, norm_mk_one n]
    push_cast
    ring
  obtain ⟨p, hp, hpm, hxp⟩ :=
    exists_natPrime_dvd_of_dvd_natCast h (m := n ^ 2 + 1) (by positivity) hxdvd
  have hnormdvd : ((n ^ 2 + 1 : ℕ) : ℤ) ∣ ((p ^ 2 : ℕ) : ℤ) := by
    obtain ⟨y, hy⟩ := hxp
    refine ⟨y.norm, ?_⟩
    have hcongr := congrArg Zsqrtd.norm hy
    rw [Zsqrtd.norm_mul, hx, norm_mk_one n] at hcongr
    push_cast at hcongr ⊢
    simpa [Zsqrtd.norm, sq] using hcongr
  have hnormdvd' : (n ^ 2 + 1) ∣ p ^ 2 := by exact_mod_cast hnormdvd
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).1 hnormdvd'
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn0
  have hp2 : 2 ≤ p := hp.two_le
  interval_cases k
  · exfalso
    rw [pow_zero] at hkeq
    nlinarith
  · rw [pow_one] at hkeq
    rw [hkeq]
    exact hp
  · exfalso
    have hlt : n < p := by nlinarith
    nlinarith

/-- **Equivalence**: `n + i` is a Gaussian prime iff `n ^ 2 + 1` is a rational prime. -/
theorem gaussianPrime_iff_prime_sq_add_one (n : ℕ) :
    Prime (⟨(n : ℤ), 1⟩ : GaussianInt) ↔ Nat.Prime (n ^ 2 + 1) :=
  ⟨prime_sq_add_one_of_gaussianPrime, gaussianPrime_of_prime_sq_add_one⟩

/-- The set of Landau primes is the image of the set of Gaussian bases under `n ↦ n ^ 2 + 1`. -/
theorem landauPrimes_eq_image :
    landauPrimes = (fun n : ℕ => n ^ 2 + 1) '' gaussianBases := by
  ext p
  constructor
  · rintro ⟨hp, n, rfl⟩
    exact ⟨n, (gaussianPrime_iff_prime_sq_add_one n).2 hp, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨(gaussianPrime_iff_prime_sq_add_one n).1 hn, n, rfl⟩

/-- **Reformulation**: Landau's fourth conjecture is equivalent to the existence of
infinitely many Gaussian primes of the form `n + i`. -/
theorem landauFourth_iff_gaussian : LandauFourthStatement ↔ GaussianPrimeFormulation := by
  rw [LandauFourthStatement, GaussianPrimeFormulation, landauPrimes_eq_image]
  exact Set.infinite_image_iff (fun a _ b _ hab => by simpa using hab)

/-- **Landau's fourth conjecture**, conditional on its Gaussian reformulation:
if there are infinitely many Gaussian primes of the form `n + i` (`n : ℕ`), then there
are infinitely many rational primes of the form `n ^ 2 + 1`.

Landau's fourth problem is a well-known open problem; what is established here is a
Lean-checked reduction of it to a statement about Gaussian primes, which
`landauFourth_iff_gaussian` shows to be equivalent to it. -/
theorem LandauFourthConjecture (h : GaussianPrimeFormulation) : LandauFourthStatement :=
  landauFourth_iff_gaussian.2 h

/-! ## Unconditional partial results -/

/-- There are infinitely many primes dividing some value of `n ^ 2 + 1`. -/
theorem infinite_primes_dvd_sq_add_one :
    {p : ℕ | Nat.Prime p ∧ ∃ n : ℕ, p ∣ n ^ 2 + 1}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  set m : ℕ := (Nat.factorial a) ^ 2 + 1 with hm
  have hfacpos : 0 < Nat.factorial a := Nat.factorial_pos a
  have hm1 : m ≠ 1 := by
    have : 1 ≤ (Nat.factorial a) ^ 2 := Nat.one_le_pow _ _ hfacpos
    omega
  have hp : Nat.Prime m.minFac := Nat.minFac_prime hm1
  refine ⟨m.minFac, ⟨hp, Nat.factorial a, Nat.minFac_dvd m⟩, ?_⟩
  by_contra hle
  push_neg at hle
  have hdvd : m.minFac ∣ Nat.factorial a := Nat.dvd_factorial hp.pos hle
  have h2 : m.minFac ∣ (Nat.factorial a) ^ 2 := hdvd.trans (dvd_pow_self _ two_ne_zero)
  have h3 : m.minFac ∣ 1 := (Nat.dvd_add_right h2).1 (Nat.minFac_dvd m)
  exact hp.ne_one (Nat.dvd_one.1 h3)

/-- A prime divides some value of `n ^ 2 + 1` iff it is `2` or is `1` mod `4`. -/
theorem prime_dvd_sq_add_one_iff {p : ℕ} (hp : Nat.Prime p) :
    (∃ n : ℕ, p ∣ n ^ 2 + 1) ↔ (p = 2 ∨ p % 4 = 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨n, hn⟩
    have h0 : ((n : ZMod p)) ^ 2 + 1 = 0 := by
      have h := (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) p).2 hn
      push_cast at h
      exact h
    have hsq : IsSquare (-1 : ZMod p) := ⟨(n : ZMod p), by linear_combination -h0⟩
    have h3 : p % 4 ≠ 3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).1 hsq
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · intro h
    have h3 : p % 4 ≠ 3 := by rcases h with rfl | h <;> omega
    obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 h3
    refine ⟨y.val, (ZMod.natCast_eq_zero_iff _ p).1 ?_⟩
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rw [sq, ← hy]
    ring

/-- There are also infinitely many `n` for which `n ^ 2 + 1` is *not* prime. -/
theorem infinite_not_prime_sq_add_one :
    {n : ℕ | ¬ Nat.Prime (n ^ 2 + 1)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨5 * (a + 1) + 2, ?_, by omega⟩
  have hfac : (5 * (a + 1) + 2) ^ 2 + 1 = 5 * (5 * (a + 1) ^ 2 + 4 * (a + 1) + 1) := by ring
  simp only [Set.mem_setOf_eq, hfac]
  exact Nat.not_prime_mul (by norm_num) (by nlinarith)

/-- Sanity check: the first few Landau primes. -/
example : IsLandauPrime 2 := ⟨by norm_num, 1, by norm_num⟩
example : IsLandauPrime 5 := ⟨by norm_num, 2, by norm_num⟩
example : IsLandauPrime 17 := ⟨by norm_num, 4, by norm_num⟩
example : IsLandauPrime 101 := ⟨by norm_num, 10, by norm_num⟩

end Brockian.LandauNSquaredPlusOne

