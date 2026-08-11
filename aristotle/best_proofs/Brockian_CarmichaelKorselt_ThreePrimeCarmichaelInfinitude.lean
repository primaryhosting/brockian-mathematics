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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` which is a Fermat pseudoprime to every base,
i.e. `n ∣ a ^ n - a` for all integers `a`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℤ, (n : ℤ) ∣ a ^ n - a

/-- Chernick's universal form: `k` gives a *Chernick triple* when `6k+1`, `12k+1` and `18k+1`
are all prime. -/
def ChernickTriple (k : ℕ) : Prop :=
  Nat.Prime (6 * k + 1) ∧ Nat.Prime (12 * k + 1) ∧ Nat.Prime (18 * k + 1)

/-- The Chernick number `(6k+1)(12k+1)(18k+1)`. -/
def chernickNum (k : ℕ) : ℕ := (6 * k + 1) * (12 * k + 1) * (18 * k + 1)

/-- The Korselt-type step: if `p` is prime and `n ≡ 1 [MOD p-1]` (written as `n = 1 + (p-1)*t`),
then `p ∣ a ^ n - a` for every integer `a`. -/
theorem prime_dvd_pow_sub_self {p n t : ℕ} (hp : p.Prime) (hn : n = 1 + (p - 1) * t) (a : ℤ) :
    (p : ℤ) ∣ a ^ n - a := by
  haveI := Fact.mk hp
  have key : ((a ^ n - a : ℤ) : ZMod p) = 0 := by
    push_cast
    subst hn
    set b : ZMod p := (a : ZMod p) with hb
    rcases eq_or_ne b 0 with h | h
    · simp [h, pow_add]
    · rw [pow_add, pow_one, pow_mul, ZMod.pow_card_sub_one_eq_one h, one_pow, mul_one, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp key

/-- The expansion `(6k+1)(12k+1)(18k+1) = 1 + 36k(36k² + 11k + 1)`. -/
theorem chernickNum_eq (k : ℕ) :
    chernickNum k = 1 + 36 * k * (36 * k ^ 2 + 11 * k + 1) := by
  unfold chernickNum; ring

theorem chernick_pos {k : ℕ} (h : ChernickTriple k) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exfalso; subst hk; have := h.1; norm_num at this
  · exact hk

/-- Chernick's theorem: if `6k+1`, `12k+1`, `18k+1` are all prime, then their product is a
Carmichael number. -/
theorem isCarmichael_chernickNum {k : ℕ} (h : ChernickTriple k) :
    IsCarmichael (chernickNum k) := by
  obtain ⟨hp, hq, hr⟩ := h
  have hk : 0 < k := chernick_pos ⟨hp, hq, hr⟩
  set X : ℕ := 36 * k ^ 2 + 11 * k + 1 with hX
  have hn : chernickNum k = 1 + 36 * k * X := chernickNum_eq k
  have h1 : chernickNum k = 1 + ((6 * k + 1) - 1) * (6 * X) := by
    rw [hn]; simp only [Nat.add_sub_cancel]; ring
  have h2 : chernickNum k = 1 + ((12 * k + 1) - 1) * (3 * X) := by
    rw [hn]; simp only [Nat.add_sub_cancel]; ring
  have h3 : chernickNum k = 1 + ((18 * k + 1) - 1) * (2 * X) := by
    rw [hn]; simp only [Nat.add_sub_cancel]; ring
  have hpq : (6 * k + 1) ≠ (12 * k + 1) := by omega
  have hpr : (6 * k + 1) ≠ (18 * k + 1) := by omega
  have hqr : (12 * k + 1) ≠ (18 * k + 1) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hn]; nlinarith
  · intro hprime
    have hdvd : (6 * k + 1) ∣ chernickNum k :=
      ⟨(12 * k + 1) * (18 * k + 1), by unfold chernickNum; ring⟩
    rcases hprime.eq_one_or_self_of_dvd _ hdvd with hcase | hcase
    · omega
    · have hfac : chernickNum k = (6 * k + 1) * ((12 * k + 1) * (18 * k + 1)) := by
        unfold chernickNum; ring
      rw [hcase] at hfac
      nlinarith [hfac]
  · intro a
    have d1 : ((6 * k + 1 : ℕ) : ℤ) ∣ a ^ chernickNum k - a :=
      prime_dvd_pow_sub_self hp h1 a
    have d2 : ((12 * k + 1 : ℕ) : ℤ) ∣ a ^ chernickNum k - a :=
      prime_dvd_pow_sub_self hq h2 a
    have d3 : ((18 * k + 1 : ℕ) : ℤ) ∣ a ^ chernickNum k - a :=
      prime_dvd_pow_sub_self hr h3 a
    have cpq : IsCoprime ((6 * k + 1 : ℕ) : ℤ) ((12 * k + 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
    have cpr : IsCoprime ((6 * k + 1 : ℕ) : ℤ) ((18 * k + 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hr).mpr hpr)
    have cqr : IsCoprime ((12 * k + 1 : ℕ) : ℤ) ((18 * k + 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hr).mpr hqr)
    have d12 : ((6 * k + 1 : ℕ) : ℤ) * ((12 * k + 1 : ℕ) : ℤ) ∣ a ^ chernickNum k - a :=
      cpq.mul_dvd d1 d2
    have d123 : ((6 * k + 1 : ℕ) : ℤ) * ((12 * k + 1 : ℕ) : ℤ) * ((18 * k + 1 : ℕ) : ℤ) ∣
        a ^ chernickNum k - a := (cpr.mul_left cqr).mul_dvd d12 d3
    simpa [chernickNum] using d123

/-- A Chernick number has exactly three prime factors. -/
theorem primeFactors_card_chernickNum {k : ℕ} (h : ChernickTriple k) :
    (chernickNum k).primeFactors.card = 3 := by
  obtain ⟨hp, hq, hr⟩ := h
  have hk : 0 < k := chernick_pos ⟨hp, hq, hr⟩
  have e : (chernickNum k).primeFactors = {6 * k + 1, 12 * k + 1, 18 * k + 1} := by
    unfold chernickNum
    rw [Nat.primeFactors_mul (by positivity) (by positivity),
      Nat.primeFactors_mul (by positivity) (by positivity),
      hp.primeFactors, hq.primeFactors, hr.primeFactors]
    ext x; simp
  rw [e, Finset.card_insert_of_notMem (by simp; omega),
    Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]

theorem chernickNum_strictMono : StrictMono chernickNum := by
  intro a b hab
  unfold chernickNum
  have h12 : (6 * a + 1) * (12 * a + 1) < (6 * b + 1) * (12 * b + 1) := by nlinarith
  exact Nat.mul_lt_mul'' h12 (by omega)

/-- **Conditional infinitude of three-prime Carmichael numbers.**

The unconditional statement is an open problem; it would follow from Dickson's conjecture applied
to the Chernick triple `6k+1, 12k+1, 18k+1`.  Here we prove the reduction: *if* there are
infinitely many `k` for which `6k+1`, `12k+1` and `18k+1` are simultaneously prime, *then* there
are infinitely many Carmichael numbers with exactly three prime factors. -/
theorem ThreePrimeCarmichaelInfinitude
    (H : {k : ℕ | ChernickTriple k}.Infinite) :
    {n : ℕ | IsCarmichael n ∧ n.primeFactors.card = 3}.Infinite := by
  have hinj : Set.InjOn chernickNum {k : ℕ | ChernickTriple k} :=
    fun _ _ _ _ hab => chernickNum_strictMono.injective hab
  refine (H.image hinj).mono ?_
  rintro n ⟨k, hk, rfl⟩
  exact ⟨isCarmichael_chernickNum hk, primeFactors_card_chernickNum hk⟩

/-- The hypothesis is non-vacuous: `k = 1` gives the Chernick triple `7, 13, 19`. -/
theorem chernickTriple_one : ChernickTriple 1 :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/-- The smallest Carmichael number `1729 = 7 * 13 * 19` arises this way. -/
theorem isCarmichael_1729 : IsCarmichael 1729 := by
  have h := isCarmichael_chernickNum chernickTriple_one
  norm_num [chernickNum] at h
  exact h

end CarmichaelKorselt
end Brockian

