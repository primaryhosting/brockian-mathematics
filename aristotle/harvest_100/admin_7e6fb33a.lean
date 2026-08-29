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
The infinitude of amicable numbers is a well-known open problem.  What is proved here is a
*conditional reduction*: if Thabit ibn Qurra's rule produces amicable pairs for arbitrarily
large parameters (i.e. there are arbitrarily large `m` for which the three Thabit numbers
`3·2^m - 1`, `3·2^(m+1) - 1`, `9·2^(2m+1) - 1` are all prime), then there are infinitely many
amicable numbers.  The Thabit construction itself is proved unconditionally
(`Brockian.AmicableNumbers.isAmicablePair_thabit`), as is the classical example `(220, 284)`.
-/

namespace Brockian.AmicableNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- `a` and `b` form an amicable pair: they are distinct and each one's proper divisors sum to
the other, equivalently `σ a = σ b = a + b`. -/
def IsAmicablePair (a b : ℕ) : Prop :=
  a ≠ b ∧ σ 1 a = a + b ∧ σ 1 b = a + b

/-- `a` is an amicable number if it belongs to some amicable pair. -/
def IsAmicable (a : ℕ) : Prop := ∃ b, IsAmicablePair a b

/-- The Thabit condition at `m`: the three numbers occurring in Thabit ibn Qurra's rule are
prime (and `m ≥ 1`). -/
def ThabitTriple (m : ℕ) : Prop :=
  1 ≤ m ∧ Nat.Prime (3 * 2 ^ m - 1) ∧ Nat.Prime (3 * 2 ^ (m + 1) - 1) ∧
    Nat.Prime (9 * 2 ^ (2 * m + 1) - 1)

/-- The classical amicable pair. -/
theorem isAmicablePair_220_284 : IsAmicablePair 220 284 :=
  ⟨by decide, by decide, by decide⟩

private lemma sum_range_two_pow (n : ℕ) : (∑ k ∈ Finset.range n, 2 ^ k) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega

private lemma sigma_one_two_pow (n : ℕ) : σ 1 (2 ^ n) + 1 = 2 ^ (n + 1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two, sum_range_two_pow]

private lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp
  simpa [Finset.sum_range_succ, add_comm] using h

private lemma coprime_two_pow_of_odd_prime {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.Coprime (2 ^ n) p :=
  Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))

/-- Thabit ibn Qurra's rule, in the normalized parametrization `2 ^ m = B + 1`. -/
theorem isAmicablePair_of_thabit_data {m B p q r : ℕ} (hB : 2 ^ m = B + 1) (hB1 : 1 ≤ B)
    (hp : p = 3 * B + 2) (hq : q = 6 * B + 5) (hr : r = 18 * B ^ 2 + 36 * B + 17)
    (hpp : p.Prime) (hqp : q.Prime) (hrp : r.Prime) :
    IsAmicablePair (2 ^ (m + 1) * (p * q)) (2 ^ (m + 1) * r) := by
  have h2 : 2 ^ (m + 1) = 2 * B + 2 := by rw [pow_succ]; omega
  have hS : σ 1 (2 ^ (m + 1)) = 4 * B + 3 := by
    have h := sigma_one_two_pow (m + 1)
    have h4 : 2 ^ (m + 1 + 1) = 4 * B + 4 := by
      rw [pow_succ, pow_succ]; omega
    omega
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hr2 : r ≠ 2 := by nlinarith [sq_nonneg B]
  have hpq : p ≠ q := by omega
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).2 hpq
  have hc1 : Nat.Coprime (2 ^ (m + 1)) (p * q) :=
    Nat.Coprime.mul_right (coprime_two_pow_of_odd_prime hpp hp2)
      (coprime_two_pow_of_odd_prime hqp hq2)
  have hc2 : Nat.Coprime (2 ^ (m + 1)) r := coprime_two_pow_of_odd_prime hrp hr2
  have hsa : σ 1 (2 ^ (m + 1) * (p * q)) = (4 * B + 3) * ((p + 1) * (q + 1)) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hc1, hS,
      isMultiplicative_sigma.map_mul_of_coprime hcpq, sigma_one_prime hpp,
      sigma_one_prime hqp]
  have hsb : σ 1 (2 ^ (m + 1) * r) = (4 * B + 3) * (r + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hc2, hS, sigma_one_prime hrp]
  refine ⟨?_, ?_, ?_⟩
  · have hlt : p * q < r := by subst hp hq hr; nlinarith
    have h2pos : 0 < 2 ^ (m + 1) := Nat.two_pow_pos _
    exact Nat.ne_of_lt (Nat.mul_lt_mul_of_pos_left hlt h2pos)
  · rw [hsa, h2]; subst hp hq hr; ring
  · rw [hsb, h2]; subst hp hq hr; ring

/-- Thabit ibn Qurra's rule in its usual form. -/
theorem isAmicablePair_thabit {m : ℕ} (h : ThabitTriple m) :
    IsAmicablePair (2 ^ (m + 1) * ((3 * 2 ^ m - 1) * (3 * 2 ^ (m + 1) - 1)))
      (2 ^ (m + 1) * (9 * 2 ^ (2 * m + 1) - 1)) := by
  obtain ⟨hm, hp, hq, hr⟩ := h
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  set B := 2 ^ m - 1 with hBdef
  have hB : 2 ^ m = B + 1 := by omega
  have hB1 : 1 ≤ B := by omega
  have e1 : 3 * 2 ^ m - 1 = 3 * B + 2 := by omega
  have e2 : 3 * 2 ^ (m + 1) - 1 = 6 * B + 5 := by rw [pow_succ]; omega
  have e3 : 9 * 2 ^ (2 * m + 1) - 1 = 18 * B ^ 2 + 36 * B + 17 := by
    have h : 2 ^ (2 * m + 1) = 2 * (B + 1) ^ 2 := by
      rw [pow_succ, two_mul, pow_add, hB]; ring
    rw [h]
    have : 9 * (2 * (B + 1) ^ 2) = 18 * B ^ 2 + 36 * B + 18 := by ring
    omega
  exact isAmicablePair_of_thabit_data hB hB1 e1 e2 e3 hp hq hr

/-- The Thabit condition holds at `m = 1` (giving the pair `(220, 284)`). -/
theorem thabitTriple_one : ThabitTriple 1 :=
  ⟨le_refl 1, by norm_num, by norm_num, by norm_num⟩

/-- The Thabit condition holds at `m = 3` (giving the pair `(17296, 18416)`). -/
theorem thabitTriple_three : ThabitTriple 3 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The Thabit condition holds at `m = 6` (giving the pair `(9363584, 9437056)`). -/
theorem thabitTriple_six : ThabitTriple 6 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Conditional infinitude of amicable numbers.**  If Thabit's rule applies for arbitrarily
large `m`, then there are infinitely many amicable numbers. -/
theorem AmicableInfinitude (H : ∀ N : ℕ, ∃ m, N ≤ m ∧ ThabitTriple m) :
    {a : ℕ | IsAmicable a}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨m, hmN, hm⟩ := H N
  refine ⟨2 ^ (m + 1) * ((3 * 2 ^ m - 1) * (3 * 2 ^ (m + 1) - 1)),
    ⟨_, isAmicablePair_thabit hm⟩, ?_⟩
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  have hpos : 0 < (3 * 2 ^ m - 1) * (3 * 2 ^ (m + 1) - 1) :=
    Nat.mul_pos (by omega) (by omega)
  calc N < 2 ^ (m + 1) :=
        lt_of_le_of_lt hmN (lt_of_lt_of_le Nat.lt_two_pow_self
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m)))
    _ ≤ 2 ^ (m + 1) * ((3 * 2 ^ m - 1) * (3 * 2 ^ (m + 1) - 1)) :=
        Nat.le_mul_of_pos_right _ hpos

end Brockian.AmicableNumbers

