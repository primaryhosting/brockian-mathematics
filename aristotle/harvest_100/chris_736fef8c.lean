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

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

/-- `sigma1 n` is the sum of all divisors of `n`. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` is `k`-hyperperfect when `k ≥ 1` and `n = 1 + k * (σ(n) - n - 1)`, i.e. `n` exceeds `1`
by `k` times the sum of its divisors other than `1` and `n`.  The equation is written in a
subtraction-free form so that it is literally correct over `ℕ`. -/
def IsKHyperperfect (k n : ℕ) : Prop :=
  0 < k ∧ n + k * (n + 1) = 1 + k * sigma1 n

/-- `n` is hyperperfect when it is `k`-hyperperfect for some `k ≥ 1`. -/
def IsHyperperfect (n : ℕ) : Prop := ∃ k, IsKHyperperfect k n

/-- The sum of divisors of a product of two distinct primes. -/
theorem sigma1_mul_of_distinct_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    sigma1 (p * q) = (1 + p) * (1 + q) := by
  unfold sigma1
  rw [Nat.Coprime.sum_divisors_mul ((Nat.coprime_primes hp hq).2 hpq),
    hp.divisors, hq.divisors, Finset.sum_pair hp.one_lt.ne, Finset.sum_pair hq.one_lt.ne]

/-- A *seed* is a natural number `m` such that both `m + 1` and `m² + m + 1` are prime.
Each seed produces an `m`-hyperperfect number, namely `(m + 1) * (m² + m + 1)`. -/
def HyperperfectSeed (m : ℕ) : Prop := (m + 1).Prime ∧ (m * m + m + 1).Prime

/-- The key construction: if `m + 1` and `m² + m + 1` are both prime, then their product is
an `m`-hyperperfect number. -/
theorem isKHyperperfect_of_seed {m : ℕ} (h : HyperperfectSeed m) :
    IsKHyperperfect m ((m + 1) * (m * m + m + 1)) := by
  obtain ⟨hp, hq⟩ := h
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (h0 ▸ hp) (by norm_num)
    · exact h0
  have hne : m + 1 ≠ m * m + m + 1 := by
    have hmm : 0 < m * m := Nat.mul_pos hm hm
    omega
  refine ⟨hm, ?_⟩
  rw [sigma1_mul_of_distinct_primes hp hq hne]
  ring

/-- Every seed gives a hyperperfect number. -/
theorem isHyperperfect_of_seed {m : ℕ} (h : HyperperfectSeed m) :
    IsHyperperfect ((m + 1) * (m * m + m + 1)) :=
  ⟨m, isKHyperperfect_of_seed h⟩

/-!
## The Brockian conjecture on hyperperfect numbers

Whether there are infinitely many hyperperfect numbers is open (it already contains the
infinitude of perfect numbers, which are exactly the `1`-hyperperfect numbers, as a special
case).  What follows is a Lean-checked *conditional reduction*: the infinitude of hyperperfect
numbers follows from the (conjectural, but Bunyakovsky/Schinzel-type) statement that there are
infinitely many `m` for which `m + 1` and `m² + m + 1` are both prime.
-/

/-- **Conditional infinitude of hyperperfect numbers.**  If there are infinitely many `m` such
that `m + 1` and `m * m + m + 1` are both prime, then there are infinitely many hyperperfect
numbers. -/
theorem HyperperfectInfinitude (H : {m : ℕ | HyperperfectSeed m}.Infinite) :
    {n : ℕ | IsHyperperfect n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨m, hm, hmN⟩ := H.exists_gt N
  refine ⟨(m + 1) * (m * m + m + 1), isHyperperfect_of_seed hm, ?_⟩
  calc N < m + 1 := by omega
    _ = (m + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ (m + 1) * (m * m + m + 1) := Nat.mul_le_mul_left _ (by omega)

/-- The `1`-hyperperfect numbers are exactly the perfect numbers. -/
theorem isKHyperperfect_one_iff_perfect {n : ℕ} (hn : 0 < n) :
    IsKHyperperfect 1 n ↔ n.Perfect := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hn]
  constructor
  · rintro ⟨-, h⟩
    simp only [sigma1, one_mul] at h
    omega
  · intro h
    refine ⟨Nat.one_pos, ?_⟩
    simp only [sigma1, one_mul]
    omega

/-- Since perfect numbers are hyperperfect, the (open) infinitude of perfect numbers is a second
sufficient condition for the infinitude of hyperperfect numbers. -/
theorem infinite_hyperperfect_of_infinite_perfect (H : {n : ℕ | n.Perfect}.Infinite) :
    {n : ℕ | IsHyperperfect n}.Infinite := by
  refine H.mono ?_
  intro n hn
  exact ⟨1, (isKHyperperfect_one_iff_perfect hn.2).2 hn⟩

/-!
## Sample hyperperfect numbers

Unconditional verifications of small instances (including `28` and `325`, which lie outside the
family above).
-/

set_option maxRecDepth 40000 in
example : IsKHyperperfect 1 6 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 40000 in
example : IsKHyperperfect 2 21 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 40000 in
example : IsKHyperperfect 1 28 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 100000 in
example : IsKHyperperfect 3 325 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 100000 in
example : IsKHyperperfect 6 301 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 100000 in
example : IsKHyperperfect 12 697 := ⟨by norm_num, by decide⟩

/-- `6` arises from the seed `m = 1`, `21` from `m = 2`, `301` from `m = 6`. -/
example : HyperperfectSeed 1 ∧ HyperperfectSeed 2 ∧ HyperperfectSeed 6 :=
  ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

end Brockian.HyperperfectNumbers

