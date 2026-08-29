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
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of Mersenne primes is a famous open problem, so what is established here is a
*Lean-checked reduction*: the statement is shown to be equivalent to the infinitude of even
perfect numbers, via the Euclid–Euler correspondence `p ↦ 2 ^ (p - 1) * (2 ^ p - 1)`.

The target declaration `Brockian.MersennePerfect.MersennePrimeInfinitude` is therefore a
conditional theorem: *if* there are infinitely many even perfect numbers, *then* there are
infinitely many Mersenne primes.  The converse implication, and the resulting equivalence, are
also proved, as is a contrapositive/boundedness reformulation.
-/

namespace Brockian.MersennePerfect

open scoped Nat

/-- The set of exponents `p` for which `2 ^ p - 1` is a (Mersenne) prime.  Such a `p` is
automatically prime itself (see `mersenneExponents_eq`). -/
def mersenneExponents : Set ℕ := {p : ℕ | Nat.Prime (2 ^ p - 1)}

/-- The set of even perfect numbers. -/
def evenPerfects : Set ℕ := {n : ℕ | Even n ∧ Nat.Perfect n}

/-- The Euclid map sending an exponent `p` to the number `2 ^ (p - 1) * (2 ^ p - 1)`. -/
def euclidMap (p : ℕ) : ℕ := 2 ^ (p - 1) * (2 ^ p - 1)

lemma mersenne_eq (p : ℕ) : mersenne p = 2 ^ p - 1 := rfl

/-- An exponent of a Mersenne prime is itself prime, so `mersenneExponents` really is the set of
exponents of Mersenne primes. -/
theorem mersenneExponents_eq :
    mersenneExponents = {p : ℕ | Nat.Prime p ∧ Nat.Prime (2 ^ p - 1)} := by
  ext p
  simp only [mersenneExponents, Set.mem_setOf_eq]
  exact ⟨fun h => ⟨Nat.Prime.of_mersenne h, h⟩, fun h => h.2⟩

lemma one_le_of_mem_mersenneExponents {p : ℕ} (hp : p ∈ mersenneExponents) : 1 ≤ p := by
  rcases Nat.eq_zero_or_pos p with rfl | h
  · simp only [mersenneExponents, Set.mem_setOf_eq, pow_zero] at hp
    exact absurd hp (by norm_num [Nat.not_prime_zero])
  · exact h

/-- Euclid's direction: the image of a Mersenne exponent is an even perfect number. -/
theorem euclidMap_mem_evenPerfects {p : ℕ} (hp : p ∈ mersenneExponents) :
    euclidMap p ∈ evenPerfects := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos
    (one_le_of_mem_mersenneExponents hp)).symm⟩
  have hpr : Nat.Prime (mersenne (k + 1)) := hp
  refine ⟨?_, ?_⟩
  · simpa [euclidMap, mersenne_eq] using
      Theorems100.Nat.even_two_pow_mul_mersenne_of_prime k hpr
  · simpa [euclidMap, mersenne_eq] using
      Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime k hpr

/-- Euler's direction: every even perfect number is in the image of `euclidMap`. -/
theorem evenPerfects_subset_image : evenPerfects ⊆ euclidMap '' mersenneExponents := by
  rintro n ⟨hev, hperf⟩
  obtain ⟨k, hpr, rfl⟩ :=
    Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect hev hperf
  exact ⟨k + 1, hpr, by simp [euclidMap, mersenne_eq]⟩

/-- The even perfect numbers are exactly the images of the Mersenne exponents. -/
theorem evenPerfects_eq_image : evenPerfects = euclidMap '' mersenneExponents := by
  refine Set.Subset.antisymm evenPerfects_subset_image ?_
  rintro _ ⟨p, hp, rfl⟩
  exact euclidMap_mem_evenPerfects hp

lemma euclidMap_strict_lt {p q : ℕ} (hp : 1 ≤ p) (hpq : p < q) : euclidMap p < euclidMap q := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  have hab : a < b := by omega
  have h1 : euclidMap (a + 1) < 2 ^ (2 * a + 1) := by
    have hlt : (2 : ℕ) ^ (a + 1) - 1 < 2 ^ (a + 1) := by
      have : (0 : ℕ) < 2 ^ (a + 1) := pow_pos (by norm_num) _
      omega
    calc euclidMap (a + 1) = 2 ^ a * (2 ^ (a + 1) - 1) := by simp [euclidMap]
      _ < 2 ^ a * 2 ^ (a + 1) := by gcongr
      _ = 2 ^ (2 * a + 1) := by ring
  have h2 : (2 : ℕ) ^ (2 * b) ≤ euclidMap (b + 1) := by
    have hb : (2 : ℕ) ^ b ≤ 2 ^ (b + 1) - 1 := by
      have h : (2 : ℕ) ^ (b + 1) = 2 * 2 ^ b := by ring
      have : (1 : ℕ) ≤ 2 ^ b := Nat.one_le_two_pow
      omega
    calc (2 : ℕ) ^ (2 * b) = 2 ^ b * 2 ^ b := by ring
      _ ≤ 2 ^ b * (2 ^ (b + 1) - 1) := Nat.mul_le_mul_left _ hb
      _ = euclidMap (b + 1) := by simp [euclidMap]
  have h3 : (2 : ℕ) ^ (2 * a + 1) ≤ 2 ^ (2 * b) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- `euclidMap` is injective on the set of Mersenne exponents. -/
theorem euclidMap_injOn : Set.InjOn euclidMap mersenneExponents := by
  intro p hp q hq h
  rcases lt_trichotomy p q with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (euclidMap_strict_lt (one_le_of_mem_mersenneExponents hp) hlt))
  · exact heq
  · exact absurd h.symm
      (Nat.ne_of_lt (euclidMap_strict_lt (one_le_of_mem_mersenneExponents hq) hgt))

/-- **Reduction.** There are infinitely many Mersenne primes if and only if there are infinitely
many even perfect numbers. -/
theorem mersenneExponents_infinite_iff : mersenneExponents.Infinite ↔ evenPerfects.Infinite := by
  rw [evenPerfects_eq_image]
  constructor
  · intro h
    exact h.image euclidMap_injOn
  · intro h
    by_contra hfin
    rw [Set.not_infinite] at hfin
    exact h (hfin.image euclidMap)

/-- **Target (conditional reduction).** If there are infinitely many even perfect numbers, then
there are infinitely many Mersenne primes, i.e. infinitely many primes `p` with `2 ^ p - 1`
prime. -/
theorem MersennePrimeInfinitude (h : {n : ℕ | Even n ∧ Nat.Perfect n}.Infinite) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (2 ^ p - 1)}.Infinite := by
  rw [← mersenneExponents_eq]
  exact mersenneExponents_infinite_iff.2 h

/-- The converse reduction: infinitely many Mersenne primes yields infinitely many even perfect
numbers. -/
theorem evenPerfect_infinitude_of_mersennePrimeInfinitude
    (h : {p : ℕ | Nat.Prime p ∧ Nat.Prime (2 ^ p - 1)}.Infinite) :
    {n : ℕ | Even n ∧ Nat.Perfect n}.Infinite := by
  rw [← mersenneExponents_eq] at h
  exact mersenneExponents_infinite_iff.1 h

/-- Reformulation of the infinitude of Mersenne primes as unboundedness of the set of
Mersenne exponents. -/
theorem mersenneExponents_infinite_iff_unbounded :
    mersenneExponents.Infinite ↔ ∀ N : ℕ, ∃ p ∈ mersenneExponents, N < p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hNp⟩ := h.exists_gt N
    exact ⟨p, hp, hNp⟩
  · exact Set.infinite_of_forall_exists_gt

/-- Sanity check that the sets are non-degenerate: `2` is a Mersenne exponent (`2 ^ 2 - 1 = 3`). -/
theorem two_mem_mersenneExponents : 2 ∈ mersenneExponents := by
  norm_num [mersenneExponents]

/-- Sanity check: `6` is an even perfect number, obtained from the Mersenne exponent `2`. -/
theorem six_mem_evenPerfects : 6 ∈ evenPerfects := by
  simpa [euclidMap] using euclidMap_mem_evenPerfects two_mem_mersenneExponents

/-- Contrapositive form: if only finitely many exponents give Mersenne primes, then there are
only finitely many even perfect numbers. -/
theorem evenPerfects_finite_of_mersenneExponents_finite
    (h : ¬ mersenneExponents.Infinite) : ¬ evenPerfects.Infinite :=
  fun hinf => h (mersenneExponents_infinite_iff.2 hinf)

/-! ### The Mersenne primes themselves -/

/-- The set of Mersenne primes: primes of the form `2 ^ p - 1`. -/
def mersennePrimes : Set ℕ := {q : ℕ | Nat.Prime q ∧ ∃ p : ℕ, q = 2 ^ p - 1}

/-- The Mersenne primes are exactly the values `2 ^ p - 1` at Mersenne exponents `p`. -/
theorem mersennePrimes_eq_image : mersennePrimes = (fun p => 2 ^ p - 1) '' mersenneExponents := by
  ext q
  constructor
  · rintro ⟨hq, p, rfl⟩
    exact ⟨p, hq, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp, p, rfl⟩

/-- Counting Mersenne primes and counting their exponents give the same notion of infinitude. -/
theorem mersennePrimes_infinite_iff : mersennePrimes.Infinite ↔ mersenneExponents.Infinite := by
  rw [mersennePrimes_eq_image]
  constructor
  · intro h
    by_contra hfin
    rw [Set.not_infinite] at hfin
    exact h (hfin.image _)
  · intro h
    exact h.image (Set.injOn_of_injective (f := fun p => 2 ^ p - 1)
      (fun a b hab => strictMono_mersenne.injective (a₁ := a) (a₂ := b) hab))

/-- **Master equivalence.** The infinitude of Mersenne primes, of their exponents, and of the even
perfect numbers are all equivalent, and each is equivalent to the corresponding unboundedness
statement. -/
theorem mersenne_infinitude_tfae :
    List.TFAE [mersennePrimes.Infinite,
      mersenneExponents.Infinite,
      evenPerfects.Infinite,
      (∀ N : ℕ, ∃ p ∈ mersenneExponents, N < p),
      (∀ N : ℕ, ∃ n ∈ evenPerfects, N < n)] := by
  tfae_have 1 ↔ 2 := mersennePrimes_infinite_iff
  tfae_have 2 ↔ 3 := mersenneExponents_infinite_iff
  tfae_have 2 ↔ 4 := mersenneExponents_infinite_iff_unbounded
  tfae_have 3 → 5 := by
    intro h N
    obtain ⟨n, hn, hNn⟩ := h.exists_gt N
    exact ⟨n, hn, hNn⟩
  tfae_have 5 → 3 := Set.infinite_of_forall_exists_gt
  tfae_finish

/-! ### A Lucas–Lehmer sufficient criterion -/

/-- If infinitely many exponents `p > 1` pass the Lucas–Lehmer test, then there are infinitely
many Mersenne primes.  (Mathlib provides sufficiency of the Lucas–Lehmer test.) -/
theorem mersennePrimes_infinite_of_lucasLehmer
    (h : {p : ℕ | 1 < p ∧ LucasLehmerTest p}.Infinite) : mersennePrimes.Infinite := by
  rw [mersennePrimes_infinite_iff]
  refine h.mono ?_
  rintro p ⟨hp, htest⟩
  exact lucas_lehmer_sufficiency p hp htest

/-- Concretely: the conditional target restated purely in terms of even perfect numbers being
unbounded. -/
theorem mersennePrimeInfinitude_of_evenPerfect_unbounded
    (h : ∀ N : ℕ, ∃ n, Even n ∧ Nat.Perfect n ∧ N < n) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (2 ^ p - 1)}.Infinite := by
  refine MersennePrimeInfinitude ?_
  have h5 : ∀ N : ℕ, ∃ n ∈ evenPerfects, N < n := by
    intro N
    obtain ⟨n, hev, hperf, hN⟩ := h N
    exact ⟨n, ⟨hev, hperf⟩, hN⟩
  exact (mersenne_infinitude_tfae.out 4 2).1 h5

/-! ### An unconditional partial result

While the infinitude of Mersenne *primes* is open, one can prove unconditionally that infinitely
many primes occur as divisors of Mersenne numbers `2 ^ p - 1` with `p` prime: any prime divisor
`q` of `2 ^ p - 1` (with `p` prime) satisfies `q ≡ 1 [MOD p]`, hence `p < q`. -/

/-- Any prime divisor of `2 ^ p - 1`, for `p` prime, exceeds `p`. -/
theorem lt_of_prime_dvd_mersenne {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hdvd : q ∣ 2 ^ p - 1) : p < q := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h1 : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
  have hmod : (2 : ℕ) ^ p ≡ 1 [MOD q] := ((Nat.modEq_iff_dvd' h1).2 hdvd).symm
  have hz : (2 : ZMod q) ^ p = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ q).2 hmod
    push_cast at h
    exact h
  have h2ne : (2 : ZMod q) ≠ 0 := by
    intro h
    have hdvd2 : q ∣ 2 := by
      have : ((2 : ℕ) : ZMod q) = 0 := by push_cast; exact h
      exact (ZMod.natCast_eq_zero_iff 2 q).1 this
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 hdvd2
    subst hq2
    have hpow : (2 : ℕ) ∣ 2 ^ p := dvd_pow_self 2 hp.ne_zero
    omega
  have hord : orderOf (2 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one hz
  have hordne : orderOf (2 : ZMod q) ≠ 1 := by
    intro h
    have h21 : (2 : ZMod q) = 1 := orderOf_eq_one_iff.1 h
    have : (1 : ZMod q) = 0 := by linear_combination h21
    exact one_ne_zero this
  have hordp : orderOf (2 : ZMod q) = p := (hp.eq_one_or_self_of_dvd _ hord).resolve_left hordne
  have hfermat : orderOf (2 : ZMod q) ∣ q - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2ne)
  rw [hordp] at hfermat
  have hq2le : 2 ≤ q := hq.two_le
  have hle : p ≤ q - 1 := Nat.le_of_dvd (by omega) hfermat
  omega

/-- The set of primes dividing some Mersenne number `2 ^ p - 1` with `p` prime. -/
def mersenneDivisorPrimes : Set ℕ := {q : ℕ | Nat.Prime q ∧ ∃ p : ℕ, Nat.Prime p ∧ q ∣ 2 ^ p - 1}

/-- **Unconditional partial result.** There are infinitely many primes dividing Mersenne numbers
with prime exponent.  (If, for infinitely many primes `p`, the number `2 ^ p - 1` is itself prime,
this set is exactly the set of Mersenne primes; in general it is larger.) -/
theorem mersenneDivisorPrimes_infinite : mersenneDivisorPrimes.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (N + 1)
  have h4 : (4 : ℕ) ≤ 2 ^ p := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
  have hm1 : 1 < 2 ^ p - 1 := by omega
  have hq : Nat.Prime (2 ^ p - 1).minFac := Nat.minFac_prime (by omega)
  refine ⟨(2 ^ p - 1).minFac, ⟨hq, p, hp, Nat.minFac_dvd _⟩, ?_⟩
  have := lt_of_prime_dvd_mersenne hp hq (Nat.minFac_dvd _)
  omega

/-- Every Mersenne prime with prime exponent belongs to `mersenneDivisorPrimes`, so the
unconditional result above is a genuine weakening of the target statement. -/
theorem mersennePrimes_subset_mersenneDivisorPrimes :
    (fun p => 2 ^ p - 1) '' mersenneExponents ⊆ mersenneDivisorPrimes := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨hp, p, Nat.Prime.of_mersenne hp, dvd_refl _⟩

/-! ### Machine-checked instances

A verified table of Mersenne exponents (certified by kernel reduction through Mathlib's
Lucas–Lehmer `norm_num` extension) and the even perfect numbers they produce. -/

/-- Passing the Lucas–Lehmer test certifies membership in `mersenneExponents`. -/
theorem mem_mersenneExponents_of_lucasLehmer {p : ℕ} (h1 : 1 < p) (h : LucasLehmerTest p) :
    p ∈ mersenneExponents :=
  lucas_lehmer_sufficiency p h1 h

/-- The first twelve Mersenne exponents, each certified in Lean. -/
theorem knownMersenneExponents :
    ↑({2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127} : Finset ℕ) ⊆ mersenneExponents := by
  intro p hp
  rw [Finset.mem_coe] at hp
  fin_cases hp
  · show Nat.Prime (2 ^ 2 - 1)
    norm_num
  all_goals exact mem_mersenneExponents_of_lucasLehmer (by norm_num) (by norm_num)

/-- Consequently there are at least twelve Mersenne primes. -/
theorem exists_twelve_mersenneExponents :
    ∃ S : Finset ℕ, S.card = 12 ∧ ↑S ⊆ mersenneExponents :=
  ⟨{2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127}, by decide, knownMersenneExponents⟩

/-- The four smallest even perfect numbers, obtained from the Mersenne exponents `2, 3, 5, 7`. -/
theorem knownEvenPerfects : ({6, 28, 496, 8128} : Set ℕ) ⊆ evenPerfects := by
  have h : ∀ p ∈ ({2, 3, 5, 7} : Finset ℕ), euclidMap p ∈ evenPerfects := by
    intro p hp
    exact euclidMap_mem_evenPerfects (knownMersenneExponents (by
      rw [Finset.mem_coe]
      fin_cases hp <;> decide))
  rintro n (rfl | rfl | rfl | rfl)
  · simpa [euclidMap] using h 2 (by decide)
  · simpa [euclidMap] using h 3 (by decide)
  · simpa [euclidMap] using h 5 (by decide)
  · simpa [euclidMap] using h 7 (by decide)

end Brockian.MersennePerfect

