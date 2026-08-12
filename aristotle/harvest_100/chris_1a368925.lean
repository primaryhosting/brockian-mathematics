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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th repunit `R n = 1 + 10 + ⋯ + 10 ^ (n - 1) = (10 ^ n - 1) / 9`,
i.e. the number written with `n` ones in base ten. -/
def repunit (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, 10 ^ i

/-- The set of repunit primes. -/
def repunitPrimeSet : Set ℕ := {p : ℕ | Nat.Prime p ∧ ∃ n, p = repunit n}

/-- The set of primes dividing some (positive-index) repunit. -/
def repunitPrimeDivisorSet : Set ℕ := {p : ℕ | Nat.Prime p ∧ ∃ n, 0 < n ∧ p ∣ repunit n}

@[simp] lemma repunit_zero : repunit 0 = 0 := rfl

@[simp] lemma repunit_one : repunit 1 = 1 := rfl

lemma repunit_succ (n : ℕ) : repunit (n + 1) = repunit n + 10 ^ n := by
  simp [repunit, Finset.sum_range_succ]

/-- A subtraction-free form of the geometric sum identity over `ℕ`. -/
lemma geom_sum_rec (x k : ℕ) :
    x * (∑ i ∈ Finset.range k, x ^ i) + 1 = (∑ i ∈ Finset.range k, x ^ i) + x ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      ring_nf
      ring_nf at ih
      nlinarith [ih, pow_succ x k]

/-- `9 * R n + 1 = 10 ^ n`. -/
lemma nine_mul_repunit_add_one (n : ℕ) : 9 * repunit n + 1 = 10 ^ n := by
  have := geom_sum_rec 10 n
  simp only [repunit] at *
  omega

lemma repunit_strictMono : StrictMono repunit := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  have : 0 < 10 ^ n := Nat.pow_pos (by norm_num)
  simp [repunit_succ, this]

lemma repunit_injective : Function.Injective repunit := repunit_strictMono.injective

lemma repunit_eq_one_iff {n : ℕ} : repunit n = 1 ↔ n = 1 := by
  constructor
  · intro h
    exact repunit_injective (by simpa using h)
  · rintro rfl; rfl

/-- Multiplicative structure: `R (d * k) = R d * ∑_{i < k} (10 ^ d) ^ i`. -/
lemma repunit_mul (d k : ℕ) :
    repunit (d * k) = repunit d * ∑ i ∈ Finset.range k, (10 ^ d) ^ i := by
  set x : ℕ := 10 ^ d with hx
  set g : ℕ := ∑ i ∈ Finset.range k, x ^ i with hg
  have h1 : x * g + 1 = g + x ^ k := geom_sum_rec x k
  have h2 : 9 * repunit d + 1 = x := nine_mul_repunit_add_one d
  have h3 : 9 * repunit (d * k) + 1 = 10 ^ (d * k) := nine_mul_repunit_add_one (d * k)
  have h4 : (10 : ℕ) ^ (d * k) = x ^ k := by
    rw [hx, ← pow_mul]
  have h5 : 9 * (repunit d * g) + 1 = x ^ k := by
    have hxg : x * g = 9 * (repunit d * g) + g := by
      rw [← h2]; ring
    omega
  have h6 : 9 * repunit (d * k) + 1 = 9 * (repunit d * g) + 1 := by
    rw [h3, h4, h5]
  omega

/-- If `d ∣ n` then `R d ∣ R n`. -/
lemma repunit_dvd_repunit {d n : ℕ} (h : d ∣ n) : repunit d ∣ repunit n := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨_, repunit_mul d k⟩

/-- Unconditional partial result: if a repunit is prime, its index is prime. -/
theorem prime_index_of_prime_repunit {n : ℕ} (h : Nat.Prime (repunit n)) : Nat.Prime n := by
  have hn2 : 2 ≤ n := by
    rcases n with _ | _ | n
    · simp at h; exact absurd h (by norm_num)
    · simp at h; exact absurd h (by norm_num)
    · omega
  refine Nat.prime_def.mpr ⟨hn2, ?_⟩
  intro m hm
  have hdvd : repunit m ∣ repunit n := repunit_dvd_repunit hm
  rcases (Nat.Prime.eq_one_or_self_of_dvd h _ hdvd) with h1 | h1
  · exact Or.inl (repunit_eq_one_iff.mp h1)
  · exact Or.inr (repunit_injective h1)

/-- Every prime other than `2` and `5` divides some repunit. -/
theorem exists_repunit_dvd_of_prime {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    ∃ n, 0 < n ∧ p ∣ repunit n := by
  have hp10 : Nat.Coprime 10 p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have hle : p ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd
    have := hp.two_le
    interval_cases p <;>
      first
        | exact h2 rfl
        | exact h5 rfl
        | (revert hdvd; decide)
        | (revert hp; decide)
  have hcop : Nat.Coprime 10 (9 * p) := Nat.Coprime.mul_right (by norm_num) hp10
  set N : ℕ := 9 * p with hN
  have hN1 : 1 < N := by
    have := hp.two_le
    omega
  set n : ℕ := Nat.totient N with hn
  have hnpos : 0 < n := Nat.totient_pos.mpr (by omega)
  refine ⟨n, hnpos, ?_⟩
  have hmod : (10 : ℕ) ^ n ≡ 1 [MOD N] := Nat.ModEq.pow_totient hcop
  have hdvd : N ∣ 10 ^ n - 1 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp hmod.symm
  have hkey : 9 * p ∣ 9 * repunit n := by
    have h9 : 9 * repunit n = 10 ^ n - 1 := by
      have := nine_mul_repunit_add_one n
      omega
    rw [h9]; exact hdvd
  exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 9)).mp hkey

/-- Unconditional partial result: infinitely many primes divide some repunit. -/
theorem repunitPrimeDivisorSet_infinite : repunitPrimeDivisorSet.Infinite := by
  have hsub : {p : ℕ | Nat.Prime p} \ ({2, 5} : Set ℕ) ⊆ repunitPrimeDivisorSet := by
    rintro p ⟨hp, hne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    exact ⟨hp, exists_repunit_dvd_of_prime hp hne.1 hne.2⟩
  exact Set.Infinite.mono hsub
    (Set.Infinite.diff Nat.infinite_setOf_prime (Set.toFinite _))

/-- **Conditional reduction for the infinitude of repunit primes.**

If for every bound `N` there is an index `n > N` with `R n` prime, then the set of
repunit primes is infinite.  (The hypothesis is the "unbounded index" form of the
conjecture; the conclusion is its "infinite set" form, and the reduction uses the
strict monotonicity of `n ↦ R n`.) -/
theorem RepunitPrimeInfinitude
    (h : ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (repunit n)) :
    repunitPrimeSet.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn, hprime⟩ := h a
  refine ⟨repunit n, ⟨hprime, ⟨n, rfl⟩⟩, ?_⟩
  calc a ≤ repunit a := repunit_strictMono.le_apply
    _ < repunit n := repunit_strictMono hn

/-- The conditional reduction is in fact an equivalence: the set of repunit primes is
infinite iff there are repunit primes of arbitrarily large index. -/
theorem repunitPrimeSet_infinite_iff :
    repunitPrimeSet.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (repunit n) := by
  refine ⟨fun hinf N => ?_, RepunitPrimeInfinitude⟩
  obtain ⟨p, hp, hgt⟩ := hinf.exists_gt (repunit N)
  obtain ⟨hpp, n, rfl⟩ := hp
  exact ⟨n, repunit_strictMono.lt_iff_lt.mp hgt, hpp⟩

/-- `R 2 = 11` is a repunit prime, so the set of repunit primes is nonempty. -/
theorem repunitPrimeSet_nonempty : repunitPrimeSet.Nonempty := by
  refine ⟨11, ?_, 2, ?_⟩
  · norm_num
  · decide

end RepunitPrimes
end Brockian

