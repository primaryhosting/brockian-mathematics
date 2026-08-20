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

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th base-ten repunit `R n = 1 + 10 + ⋯ + 10 ^ (n - 1)`, i.e. the natural number
whose decimal expansion consists of `n` ones. -/
def repunit : Nat → Nat
  | 0 => 0
  | n + 1 => 10 ^ n + repunit n

/-- Primality of a natural number, spelled out: `p` is at least `2` and its only divisors
are `1` and `p`. -/
def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

@[simp] theorem repunit_zero : repunit 0 = 0 := rfl

@[simp] theorem repunit_one : repunit 1 = 1 := rfl

theorem ten_pow_pos (n : Nat) : 0 < 10 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      exact Nat.mul_pos ih (by decide)

theorem repunit_succ (n : Nat) : repunit (n + 1) = 10 ^ n + repunit n := rfl

/-- The basic splitting identity `R (m + n) = R m + 10 ^ m * R n`. -/
theorem repunit_add (m n : Nat) : repunit (m + n) = repunit m + 10 ^ m * repunit n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : m + (n + 1) = (m + n) + 1 := by omega
      rw [h, repunit_succ, ih, repunit_succ, Nat.pow_add, Nat.mul_add]
      omega

theorem repunit_lt_succ (n : Nat) : repunit n < repunit (n + 1) := by
  have := ten_pow_pos n
  rw [repunit_succ]
  omega

theorem repunit_lt_repunit {m n : Nat} (h : m < n) : repunit m < repunit n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge m n with hmn | hmn
      · exact Nat.lt_trans (ih hmn) (repunit_lt_succ n)
      · have : m = n := by omega
        subst this
        exact repunit_lt_succ m

theorem repunit_injective {m n : Nat} (h : repunit m = repunit n) : m = n := by
  rcases Nat.lt_trichotomy m n with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (repunit_lt_repunit hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (repunit_lt_repunit hgt))

theorem le_repunit (n : Nat) : n ≤ repunit n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have := ten_pow_pos n
      rw [repunit_succ]
      omega

theorem two_le_repunit {n : Nat} (h : 2 ≤ n) : 2 ≤ repunit n := by
  have h1 : repunit 1 < repunit n := repunit_lt_repunit (by omega)
  simpa using h1

/-- Repunits divide along divisibility of indices: if `d ∣ n` then `R d ∣ R n`. -/
theorem repunit_dvd_repunit_of_dvd {d n : Nat} (h : d ∣ n) : repunit d ∣ repunit n := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simp
  | succ k ih =>
      obtain ⟨a, ha⟩ := ih
      have hmul : d * (k + 1) = d * k + d := Nat.mul_succ d k
      refine ⟨a + 10 ^ (d * k), ?_⟩
      rw [hmul, repunit_add, ha, Nat.mul_add, Nat.mul_comm (repunit d) (10 ^ (d * k))]

/-- If a repunit `R n` is prime, then its index `n` is prime. -/
theorem prime_index_of_prime_repunit {n : Nat} (h : IsPrimeNat (repunit n)) : IsPrimeNat n := by
  obtain ⟨h2, hdiv⟩ := h
  have hn2 : 2 ≤ n := by
    rcases n with _ | _ | m
    · simp at h2
    · simp at h2
    · omega
  refine ⟨hn2, fun d hd => ?_⟩
  rcases hdiv (repunit d) (repunit_dvd_repunit_of_dvd hd) with h1 | h1
  · left
    exact repunit_injective (by simpa using h1)
  · right
    exact repunit_injective h1

/-- **Conditional reduction (Brockian repunit prime infinitude).**

Assume the open hypothesis that repunit primes occur with arbitrarily large index.  Then
there are infinitely many repunit primes, in the sense that for every bound `N` there is a
prime `q > N` which is a repunit.  Moreover, by `prime_index_of_prime_repunit`, every index
occurring here is itself prime, so the hypothesis is equivalent to the usual formulation
restricted to prime indices. -/
theorem RepunitPrimeInfinitude
    (h : ∀ N : Nat, ∃ n : Nat, N < n ∧ IsPrimeNat (repunit n)) :
    ∀ N : Nat, ∃ q : Nat, N < q ∧ IsPrimeNat q ∧ ∃ n : Nat, q = repunit n := by
  intro N
  obtain ⟨n, hn, hp⟩ := h N
  refine ⟨repunit n, ?_, hp, ⟨n, rfl⟩⟩
  have := le_repunit n
  omega

end RepunitPrimes
end Brockian

import Mathlib
import Brockian.RepunitPrimes

/-!
# Repunit primes: Mathlib interface

Companion module to `Brockian.RepunitPrimes` (which is deliberately kept free of imports so
that its required header docstring can appear at the very top of the file).

Here we connect the self-contained definitions used there to the standard Mathlib notions:

* `IsPrimeNat p ↔ Nat.Prime p` (`Nat.prime_def`);
* `repunit n = ∑ i ∈ Finset.range n, 10 ^ i` and `9 * repunit n + 1 = 10 ^ n`;
* the decimal expansion of `repunit n` consists of `n` ones;
* a `Set.Infinite` formulation of the conditional infinitude statement.
-/


namespace Brockian
namespace RepunitPrimes

/-- The elementary primality predicate used in `Brockian.RepunitPrimes` agrees with
`Nat.Prime`; this is `Nat.prime_def`. -/
theorem isPrimeNat_iff_nat_prime {p : ℕ} : IsPrimeNat p ↔ Nat.Prime p :=
  Nat.prime_def.symm

/-- The repunit as a geometric sum. -/
theorem repunit_eq_geom_sum (n : ℕ) : repunit n = ∑ i ∈ Finset.range n, 10 ^ i := by
  induction n with
  | zero => simp
  | succ n ih => rw [repunit_succ, ih, Finset.sum_range_succ]; ring

/-- The closed form `R n = (10 ^ n - 1) / 9`, stated without subtraction. -/
theorem nine_mul_repunit_add_one (n : ℕ) : 9 * repunit n + 1 = 10 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [repunit_succ, pow_succ]; omega

theorem repunit_eq_div (n : ℕ) : repunit n = (10 ^ n - 1) / 9 := by
  have h := nine_mul_repunit_add_one n
  omega

theorem repunit_succ' (n : ℕ) : repunit (n + 1) = 10 * repunit n + 1 := by
  have h := nine_mul_repunit_add_one n
  rw [repunit_succ]
  omega

/-- The decimal expansion of `repunit n` is a string of `n` ones. -/
theorem digits_repunit (n : ℕ) : Nat.digits 10 (repunit n) = List.replicate n 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : 0 < repunit (n + 1) := by
        rw [repunit_succ']; omega
      rw [Nat.digits_def' (by norm_num) hpos, repunit_succ']
      have h1 : (10 * repunit n + 1) % 10 = 1 := by omega
      have h2 : (10 * repunit n + 1) / 10 = repunit n := by omega
      rw [h1, h2, ih, List.replicate_succ]

@[simp] theorem repunit_two : repunit 2 = 11 := by decide

@[simp] theorem repunit_three : repunit 3 = 111 := by decide

/-- The hypothesis of the conditional reduction is not vacuous: `R 2 = 11` is a repunit
prime. -/
theorem prime_repunit_two : Nat.Prime (repunit 2) := by
  rw [repunit_two]; norm_num

/-- **Conditional reduction, `Set.Infinite` form.**  If repunit primes occur with
arbitrarily large index, then the set of repunit primes is infinite. -/
theorem setOf_repunit_primes_infinite
    (h : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (repunit n)) :
    {q : ℕ | q.Prime ∧ ∃ n : ℕ, q = repunit n}.Infinite := by
  have h' : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ IsPrimeNat (repunit n) := by
    intro N
    obtain ⟨n, hn, hp⟩ := h N
    exact ⟨n, hn, isPrimeNat_iff_nat_prime.mpr hp⟩
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨q, hq, hqp, n, rfl⟩ := RepunitPrimeInfinitude h' a
  exact ⟨repunit n, ⟨isPrimeNat_iff_nat_prime.mp hqp, ⟨n, rfl⟩⟩, hq⟩

end RepunitPrimes
end Brockian

