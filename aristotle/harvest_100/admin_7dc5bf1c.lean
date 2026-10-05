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

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RepunitPrimes

open Finset

/-- The `n`-th base-`b` repunit: `1 + b + b^2 + ⋯ + b^(n-1)`. -/
def repunitBase (b n : ℕ) : ℕ := ∑ i ∈ range n, b ^ i

/-- The `n`-th (decimal) repunit `R n = 11⋯1` (`n` ones), i.e. `(10^n - 1)/9`. -/
def repunit (n : ℕ) : ℕ := repunitBase 10 n

@[simp] lemma repunitBase_zero (b : ℕ) : repunitBase b 0 = 0 := by simp [repunitBase]

@[simp] lemma repunitBase_one (b : ℕ) : repunitBase b 1 = 1 := by simp [repunitBase]

lemma repunitBase_succ (b n : ℕ) : repunitBase b (n + 1) = repunitBase b n + b ^ n := by
  simp [repunitBase, Finset.sum_range_succ]

/-- The standard closed form: `9 * R n + 1 = 10 ^ n`. -/
lemma nine_mul_repunit_add_one (n : ℕ) : 9 * repunit n + 1 = 10 ^ n := by
  induction n with
  | zero => simp [repunit]
  | succ n ih =>
      rw [repunit, repunitBase_succ, ← repunit]
      ring_nf
      ring_nf at ih
      omega

/-- Multiplicativity of the index for repunits: `R_{a·b}` factors through `R_a`. -/
lemma repunitBase_mul (b a k : ℕ) :
    repunitBase b (a * k) = repunitBase b a * repunitBase (b ^ a) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h : a * (k + 1) = a * k + a := by ring
      have e1 : repunitBase b (a * k + a)
          = repunitBase b (a * k) + ∑ i ∈ range a, b ^ (a * k + i) := by
        simp only [repunitBase]; exact Finset.sum_range_add _ _ _
      rw [h, e1, ih, repunitBase_succ (b ^ a) k, Nat.mul_add]
      congr 1
      simp only [repunitBase, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_add, pow_mul, mul_comm]

/-- If `a ∣ n` then `R a ∣ R n`. -/
lemma repunit_dvd_repunit {a n : ℕ} (h : a ∣ n) : repunit a ∣ repunit n := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨repunitBase (10 ^ a) k, repunitBase_mul 10 a k⟩

lemma repunitBase_strictMono {b : ℕ} (hb : 1 ≤ b) : StrictMono (repunitBase b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [repunitBase_succ]
  have : 0 < b ^ n := pow_pos hb n
  omega

lemma repunit_strictMono : StrictMono repunit := repunitBase_strictMono (by norm_num)

lemma repunit_injective : Function.Injective repunit := repunit_strictMono.injective

lemma le_repunit (n : ℕ) : n ≤ repunit n := repunit_strictMono.le_apply

lemma one_lt_repunit {n : ℕ} (hn : 2 ≤ n) : 1 < repunit n := by
  calc 1 = repunit 1 := by simp [repunit]
  _ < repunit n := repunit_strictMono (by omega)

/-- If a repunit `R n` is prime, then its index `n` is prime. -/
theorem prime_index_of_prime_repunit {n : ℕ} (h : Nat.Prime (repunit n)) : Nat.Prime n := by
  have hn2 : 2 ≤ n := by
    by_contra hlt
    interval_cases n <;> simp [repunit, repunitBase] at h <;> norm_num at h
  refine Nat.prime_def.mpr ⟨hn2, fun d hd => ?_⟩
  rcases (Nat.dvd_prime h).mp (repunit_dvd_repunit hd) with h1 | h2
  · -- `repunit d = 1` forces `d = 1`
    left
    have : d < 2 := by
      by_contra hc
      exact absurd h1 (by have := one_lt_repunit (n := d) (by omega); omega)
    interval_cases d
    · simp [repunit] at h1
    · rfl
  · right
    exact repunit_injective h2

/-- `R 2 = 11` is a repunit prime, so repunit primes exist. -/
theorem repunit_two_prime : Nat.Prime (repunit 2) := by
  have : repunit 2 = 11 := by simp [repunit, repunitBase, Finset.sum_range_succ]
  rw [this]; norm_num

/-- The set of repunit primes. -/
def repunitPrimes : Set ℕ := {q | Nat.Prime q ∧ ∃ n, repunit n = q}

/--
**Conditional infinitude of repunit primes.**

Whether infinitely many repunits are prime is an open problem, so this is a
conditional reduction: assuming that repunit primes occur with arbitrarily large
index (equivalently, that the index set `{n | R n prime}` is unbounded), the set
of repunit *primes* itself is infinite.  The content of the reduction is that the
map `n ↦ R n` is strictly monotone, hence injective and unbounded, so infinitely
many indices really do yield infinitely many distinct primes.
-/
theorem RepunitPrimeInfinitude
    (H : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (repunit n)) :
    repunitPrimes.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨M, hM⟩
  obtain ⟨n, hn, hp⟩ := H M
  have hmem : repunit n ∈ repunitPrimes := ⟨hp, ⟨n, rfl⟩⟩
  have := hM hmem
  have := le_repunit n
  omega

/-- Equivalently: infinitely many indices give repunit primes iff there are
infinitely many repunit primes. -/
theorem repunitPrimes_infinite_iff :
    repunitPrimes.Infinite ↔ {n : ℕ | Nat.Prime (repunit n)}.Infinite := by
  constructor
  · intro h
    apply Set.infinite_of_not_bddAbove
    rintro ⟨M, hM⟩
    apply h
    apply Set.Finite.subset (Set.finite_Icc 0 (repunit M))
    rintro q ⟨hq, n, rfl⟩
    have hn : n ≤ M := hM hq
    exact ⟨Nat.zero_le _, repunit_strictMono.monotone hn⟩
  · intro h
    apply RepunitPrimeInfinitude
    intro N
    obtain ⟨n, hn, hN⟩ := h.exists_gt N
    exact ⟨n, hN, hn⟩

end Brockian.RepunitPrimes

