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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset

/-- The sum of the proper divisors of `n`. -/
def properDivisorSum (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- `m` and `n` form an amicable pair: they are distinct and each is the sum of the
proper divisors of the other. -/
def IsAmicablePair (m n : ℕ) : Prop :=
  m ≠ n ∧ properDivisorSum m = n ∧ properDivisorSum n = m

/-- `n` is an amicable number: it belongs to some amicable pair. -/
def IsAmicable (n : ℕ) : Prop := ∃ m, IsAmicablePair n m

/-- Thâbit ibn Qurra's triple condition at `m`: the three numbers
`3·2^m - 1`, `3·2^(m+1) - 1` and `9·2^(2m+1) - 1` are all prime. -/
def ThabitTriple (m : ℕ) : Prop :=
  (3 * 2 ^ m - 1).Prime ∧ (3 * 2 ^ (m + 1) - 1).Prime ∧ (9 * 2 ^ (2 * m + 1) - 1).Prime

/-! ### Elementary divisor-sum computations -/

lemma sum_divisors_two_pow (k : ℕ) : (∑ d ∈ (2 ^ k).divisors, d) + 1 = 2 ^ (k + 1) := by
  rw [← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ]; ring_nf; ring_nf at ih; omega

lemma sum_divisors_prime {p : ℕ} (hp : p.Prime) : ∑ d ∈ p.divisors, d = p + 1 := by
  rw [hp.divisors]
  simp [Finset.sum_pair hp.one_lt.ne]
  omega

/-! ### Thâbit ibn Qurra's rule -/

/-- Thâbit ibn Qurra's rule: if `p + 1 = 3·2^m`, `q + 1 = 3·2^(m+1)`, `r + 1 = 9·2^(2m+1)`
with `p`, `q`, `r` prime and `m ≥ 1`, then `2^(m+1)·p·q` and `2^(m+1)·r` are amicable. -/
theorem thabit_amicable {m p q r : ℕ} (hm : 1 ≤ m)
    (hp : p + 1 = 3 * 2 ^ m) (hq : q + 1 = 3 * 2 ^ (m + 1))
    (hr : r + 1 = 9 * 2 ^ (2 * m + 1))
    (hpp : p.Prime) (hqp : q.Prime) (hrp : r.Prime) :
    IsAmicablePair (2 ^ (m + 1) * p * q) (2 ^ (m + 1) * r) := by
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by
    have : (2:ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
    omega
  have hr2 : r ≠ 2 := by
    have : (2:ℕ) ^ (2 * m + 1) = 2 * (2 ^ m) ^ 2 := by
      rw [pow_succ, mul_comm 2 m, pow_mul]; ring
    nlinarith [h2m]
  have hpq : p ≠ q := by
    have : (2:ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
    omega
  -- coprimality of the three prime factors
  have cop2p : Nat.Coprime (2 ^ (m + 1)) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hpp).mpr (Ne.symm hp2))
  have cop2q : Nat.Coprime (2 ^ (m + 1)) q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hqp).mpr (Ne.symm hq2))
  have cop2r : Nat.Coprime (2 ^ (m + 1)) r :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hrp).mpr (Ne.symm hr2))
  have coppq : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).mpr hpq
  -- the two divisor sums, in factored form
  set S := ∑ d ∈ ((2:ℕ) ^ (m + 1)).divisors, d
  have hS : S + 1 = 2 ^ (m + 2) := sum_divisors_two_pow (m + 1)
  have hsa : ∑ d ∈ (2 ^ (m + 1) * p * q).divisors, d = S * (p + 1) * (q + 1) := by
    rw [Nat.Coprime.sum_divisors_mul (Nat.Coprime.mul_left cop2q coppq),
      Nat.Coprime.sum_divisors_mul cop2p, sum_divisors_prime hpp, sum_divisors_prime hqp]
  have hsb : ∑ d ∈ (2 ^ (m + 1) * r).divisors, d = S * (r + 1) := by
    rw [Nat.Coprime.sum_divisors_mul cop2r, sum_divisors_prime hrp]
  -- the arithmetic identities, checked over ℤ
  have e2 : ((2:ℤ) ^ (2 * m + 1)) = 2 * (2 ^ m) ^ 2 := by
    rw [pow_succ, mul_comm 2 m, pow_mul]; ring
  have hpz : (p : ℤ) = 3 * 2 ^ m - 1 := by have := hp; zify at this; linarith
  have hqz : (q : ℤ) = 6 * 2 ^ m - 1 := by
    have := hq; zify at this; ring_nf at this ⊢; linarith
  have hrz : (r : ℤ) = 18 * (2 ^ m) ^ 2 - 1 := by
    have := hr; zify at this; rw [e2] at this; linarith
  have hSz : (S : ℤ) = 4 * 2 ^ m - 1 := by
    have e : ((2:ℤ) ^ (m + 2)) = 4 * 2 ^ m := by ring
    have := hS; zify at this; rw [e] at this; linarith
  have key : S * (p + 1) * (q + 1) = 2 ^ (m + 1) * p * q + 2 ^ (m + 1) * r ∧
      S * (r + 1) = 2 ^ (m + 1) * p * q + 2 ^ (m + 1) * r := by
    constructor <;> · zify
                      have e : ((2:ℤ) ^ (m + 1)) = 2 * 2 ^ m := by ring
                      rw [hpz, hqz, hrz, hSz, e]; ring
  -- the two numbers are distinct
  have hne : 2 ^ (m + 1) * p * q ≠ 2 ^ (m + 1) * r := by
    have h2mz : (2:ℤ) ≤ 2 ^ m := by exact_mod_cast h2m
    intro h
    have h' : ((2:ℤ) ^ (m + 1) * p * q) = 2 ^ (m + 1) * r := by exact_mod_cast h
    rw [hpz, hqz, hrz] at h'
    have hpos : (0:ℤ) < 2 ^ (m + 1) := by positivity
    nlinarith [h', hpos, h2mz]
  refine ⟨hne, ?_, ?_⟩
  · have := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := 2 ^ (m + 1) * p * q)
    rw [hsa, key.1] at this
    unfold properDivisorSum
    omega
  · have := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := 2 ^ (m + 1) * r)
    rw [hsb, key.2] at this
    unfold properDivisorSum
    omega

/-- Thâbit's rule in the form of the `ThabitTriple` predicate. -/
theorem exists_amicable_of_thabitTriple {m : ℕ} (hm : 1 ≤ m) (h : ThabitTriple m) :
    IsAmicable (2 ^ (m + 1) * (9 * 2 ^ (2 * m + 1) - 1)) := by
  obtain ⟨hpp, hqp, hrp⟩ := h
  have h1 : (1:ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : (1:ℕ) ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  have h3 : (1:ℕ) ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  refine ⟨2 ^ (m + 1) * (3 * 2 ^ m - 1) * (3 * 2 ^ (m + 1) - 1), ?_⟩
  obtain ⟨hne, h₁, h₂⟩ := thabit_amicable (m := m) (p := 3 * 2 ^ m - 1)
    (q := 3 * 2 ^ (m + 1) - 1) (r := 9 * 2 ^ (2 * m + 1) - 1) hm (by omega) (by omega)
    (by omega) hpp hqp hrp
  exact ⟨hne.symm, h₂, h₁⟩

/-! ### The conditional infinitude statement -/

/-- **Conditional infinitude of amicable numbers.**  If Thâbit's triple condition holds for
infinitely many `m` (a classical open conjecture), then there are infinitely many amicable
numbers. -/
theorem AmicableInfinitude
    (hThabit : ∀ N : ℕ, ∃ m, N ≤ m ∧ ThabitTriple m) :
    {n : ℕ | IsAmicable n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt (fun N => ?_)
  obtain ⟨m, hm, htriple⟩ := hThabit (max N 1)
  have hm1 : 1 ≤ m := le_trans (le_max_right N 1) hm
  have hmN : N ≤ m := le_trans (le_max_left N 1) hm
  refine ⟨2 ^ (m + 1) * (9 * 2 ^ (2 * m + 1) - 1), exists_amicable_of_thabitTriple hm1 htriple, ?_⟩
  have h3 : (2:ℕ) ≤ 2 ^ (2 * m + 1) := by
    calc (2:ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : m < 2 ^ (m + 1) :=
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  calc N ≤ m := hmN
    _ < 2 ^ (m + 1) := hlt
    _ = 2 ^ (m + 1) * 1 := (mul_one _).symm
    _ ≤ 2 ^ (m + 1) * (9 * 2 ^ (2 * m + 1) - 1) := by
        exact Nat.mul_le_mul_left _ (by omega)

/-! ### An unconditional example -/

/-- The classical amicable pair `(220, 284)`. -/
theorem amicable_220_284 : IsAmicablePair 220 284 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> · unfold properDivisorSum; decide

/-- Thâbit's condition holds at `m = 1` (the primes `5, 11, 71`). -/
theorem thabitTriple_one : ThabitTriple 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- Thâbit's condition holds at `m = 3` (the primes `23, 47, 1151`). -/
theorem thabitTriple_three : ThabitTriple 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- The amicable pair `(17296, 18416)` produced by Thâbit's rule at `m = 3`. -/
theorem amicable_17296_18416 : IsAmicablePair 17296 18416 := by
  have h := thabit_amicable (m := 3) (p := 23) (q := 47) (r := 1151) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

end Brockian.AmicableNumbers

