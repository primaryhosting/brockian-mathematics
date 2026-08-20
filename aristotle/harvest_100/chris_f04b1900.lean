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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(A001414, the "integer logarithm"). By convention `sopfr 0 = sopfr 1 = 0`. -/
def sopfr (n : ℕ) : ℕ := n.primeFactorsList.sum

/-- `n` starts a *Ruth–Aaron pair* if `n` and `n + 1` have the same sum of prime
factors (counted with multiplicity). -/
def IsRuthAaronPair (n : ℕ) : Prop := 0 < n ∧ sopfr n = sopfr (n + 1)

/-! ### Basic arithmetic of `sopfr` -/

@[simp] theorem sopfr_one : sopfr 1 = 0 := by simp [sopfr]

theorem sopfr_prime {p : ℕ} (hp : p.Prime) : sopfr p = p := by
  simp [sopfr, Nat.primeFactorsList_prime hp]

theorem sopfr_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    sopfr (a * b) = sopfr a + sopfr b := by
  have := (Nat.perm_primeFactorsList_mul ha hb).sum_eq
  simpa [sopfr, List.sum_append] using this

/-- Multiplying by a prime adds that prime to `sopfr`. -/
theorem sopfr_prime_mul {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0) :
    sopfr (p * a) = p + sopfr a := by
  rw [sopfr_mul hp.ne_zero ha, sopfr_prime hp]

/-! ### Examples of Ruth–Aaron pairs -/

theorem sopfr_five : sopfr 5 = 5 := sopfr_prime (by norm_num)

theorem sopfr_six : sopfr 6 = 5 := by
  have h : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h, sopfr_prime_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num)]

theorem sopfr_eight : sopfr 8 = 6 := by
  have h : (8 : ℕ) = 2 * (2 * 2) := by norm_num
  rw [h, sopfr_prime_mul (by norm_num) (by norm_num),
    sopfr_prime_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num)]

theorem sopfr_nine : sopfr 9 = 6 := by
  have h : (9 : ℕ) = 3 * 3 := by norm_num
  rw [h, sopfr_prime_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num)]

theorem sopfr_fifteen : sopfr 15 = 8 := by
  have h : (15 : ℕ) = 3 * 5 := by norm_num
  rw [h, sopfr_prime_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num)]

theorem sopfr_sixteen : sopfr 16 = 8 := by
  have h : (16 : ℕ) = 2 * (2 * (2 * 2)) := by norm_num
  rw [h, sopfr_prime_mul (by norm_num) (by norm_num),
    sopfr_prime_mul (by norm_num) (by norm_num),
    sopfr_prime_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num)]

theorem sopfr_seventyseven : sopfr 77 = 18 := by
  have h : (77 : ℕ) = 7 * 11 := by norm_num
  rw [h, sopfr_prime_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num)]

theorem sopfr_seventyeight : sopfr 78 = 18 := by
  have h : (78 : ℕ) = 2 * (3 * 13) := by norm_num
  rw [h, sopfr_prime_mul (by norm_num) (by norm_num),
    sopfr_prime_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num)]

theorem sopfr_125 : sopfr 125 = 15 := by
  have h : (125 : ℕ) = 5 * (5 * 5) := by norm_num
  rw [h, sopfr_prime_mul (by norm_num) (by norm_num),
    sopfr_prime_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num)]

theorem sopfr_126 : sopfr 126 = 15 := by
  have h : (126 : ℕ) = 2 * (3 * (3 * 7)) := by norm_num
  rw [h, sopfr_prime_mul (by norm_num) (by norm_num),
    sopfr_prime_mul (by norm_num) (by norm_num),
    sopfr_prime_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num)]

theorem sopfr_714 : sopfr 714 = 29 := by
  have h : (714 : ℕ) = 2 * (3 * (7 * 17)) := by norm_num
  rw [h, sopfr_prime_mul (by norm_num) (by norm_num),
    sopfr_prime_mul (by norm_num) (by norm_num),
    sopfr_prime_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num)]

theorem sopfr_715 : sopfr 715 = 29 := by
  have h : (715 : ℕ) = 5 * (11 * 13) := by norm_num
  rw [h, sopfr_prime_mul (by norm_num) (by norm_num),
    sopfr_prime_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num)]

theorem isRuthAaronPair_five : IsRuthAaronPair 5 :=
  ⟨by norm_num, by rw [sopfr_five]; exact sopfr_six.symm⟩

theorem isRuthAaronPair_eight : IsRuthAaronPair 8 :=
  ⟨by norm_num, by rw [sopfr_eight]; exact sopfr_nine.symm⟩

theorem isRuthAaronPair_fifteen : IsRuthAaronPair 15 :=
  ⟨by norm_num, by rw [sopfr_fifteen]; exact sopfr_sixteen.symm⟩

theorem isRuthAaronPair_seventyseven : IsRuthAaronPair 77 :=
  ⟨by norm_num, by rw [sopfr_seventyseven]; exact sopfr_seventyeight.symm⟩

theorem isRuthAaronPair_125 : IsRuthAaronPair 125 :=
  ⟨by norm_num, by rw [sopfr_125]; exact sopfr_126.symm⟩

/-- The original Ruth–Aaron pair: `714 = 2·3·7·17` and `715 = 5·11·13`, both with
prime-factor sum `29`. -/
theorem isRuthAaronPair_714 : IsRuthAaronPair 714 :=
  ⟨by norm_num, by rw [sopfr_714]; exact sopfr_715.symm⟩

/-- The set of Ruth–Aaron pairs is nonempty. -/
theorem ruthAaron_nonempty : {n : ℕ | IsRuthAaronPair n}.Nonempty :=
  ⟨714, isRuthAaronPair_714⟩

/-- The first six Ruth–Aaron pairs are all Ruth–Aaron pairs. -/
theorem ruthAaron_first_six :
    ({5, 8, 15, 77, 125, 714} : Set ℕ) ⊆ {n : ℕ | IsRuthAaronPair n} := by
  rintro n (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact isRuthAaronPair_five
  · exact isRuthAaronPair_eight
  · exact isRuthAaronPair_fifteen
  · exact isRuthAaronPair_seventyseven
  · exact isRuthAaronPair_125
  · exact isRuthAaronPair_714

/-- There are at least six Ruth–Aaron pairs. -/
theorem exists_six_ruthAaronPairs :
    ∃ s : Finset ℕ, s.card = 6 ∧ ∀ n ∈ s, IsRuthAaronPair n := by
  refine ⟨{5, 8, 15, 77, 125, 714}, by decide, fun n hn => ?_⟩
  fin_cases hn
  · exact isRuthAaronPair_five
  · exact isRuthAaronPair_eight
  · exact isRuthAaronPair_fifteen
  · exact isRuthAaronPair_seventyseven
  · exact isRuthAaronPair_125
  · exact isRuthAaronPair_714

/-! ### The infinitude statement

Whether there are infinitely many Ruth–Aaron pairs is an open problem (Erdős).
The theorem below is the exact reduction of that conjecture to the statement that
Ruth–Aaron pairs are unbounded; it is proved unconditionally. -/

/-- **Ruth–Aaron infinitude, as an equivalence.** The set of Ruth–Aaron pairs is
infinite if and only if it is unbounded, i.e. iff for every `N` there is a
Ruth–Aaron pair `n > N`. (The truth of either side is the open Erdős conjecture;
this theorem is the unconditional reduction between the two formulations.) -/
theorem RuthAaronInfinitude :
    {n : ℕ | IsRuthAaronPair n}.Infinite ↔ ∀ N : ℕ, ∃ n : ℕ, N < n ∧ IsRuthAaronPair n := by
  rw [Set.infinite_iff_exists_gt]
  exact ⟨fun h N => (h N).imp fun _ hn => ⟨hn.2, hn.1⟩,
    fun h N => (h N).imp fun _ hn => ⟨hn.2, hn.1⟩⟩

/-- The same conjecture phrased with the `atTop` filter: Ruth–Aaron pairs occur
infinitely often iff they occur frequently. -/
theorem ruthAaron_infinite_iff_frequently :
    {n : ℕ | IsRuthAaronPair n}.Infinite ↔ ∃ᶠ n in Filter.atTop, IsRuthAaronPair n := by
  rw [RuthAaronInfinitude, Filter.frequently_atTop']

/-- A concrete sufficient condition: if infinitely many primes `p` satisfy
`sopfr (p + 1) = p`, then there are infinitely many Ruth–Aaron pairs.
(For example `p = 5`, since `sopfr 6 = 5`.) -/
theorem ruthAaron_infinite_of_primes
    (h : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ sopfr (p + 1) = p) :
    {n : ℕ | IsRuthAaronPair n}.Infinite := by
  refine RuthAaronInfinitude.mpr fun N => ?_
  obtain ⟨p, hNp, hp, hsum⟩ := h N
  exact ⟨p, hNp, hp.pos, by rw [sopfr_prime hp, hsum]⟩

/-! ### The squarefree (distinct primes) variant

The variant conjecture uses `sopf`, the sum of the *distinct* prime factors.
It is likewise open, and admits the same reduction. -/

/-- `sopf n` is the sum of the distinct prime factors of `n` (A008472). -/
def sopf (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, p

/-- `n` starts a Ruth–Aaron pair in the *distinct primes* sense. -/
def IsWeakRuthAaronPair (n : ℕ) : Prop := 0 < n ∧ sopf n = sopf (n + 1)

theorem sopf_prime {p : ℕ} (hp : p.Prime) : sopf p = p := by
  simp [sopf, hp.primeFactors]

theorem sopf_24 : sopf 24 = 5 := by
  have h : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  have : Nat.primeFactors 24 = {2, 3} := by
    rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) (by norm_num),
      Nat.Prime.primeFactors (by norm_num)]
    decide
  rw [sopf, this]
  decide

theorem sopf_25 : sopf 25 = 5 := by
  have h : (25 : ℕ) = 5 ^ 2 := by norm_num
  rw [sopf, h, Nat.primeFactors_prime_pow (by norm_num) (by norm_num)]
  decide

/-- `(24, 25)` is a Ruth–Aaron pair for the sum of distinct prime factors:
`24 = 2^3·3` and `25 = 5^2` both give `5`. -/
theorem isWeakRuthAaronPair_24 : IsWeakRuthAaronPair 24 :=
  ⟨by norm_num, by rw [sopf_24]; exact sopf_25.symm⟩

/-- The same reduction for the distinct-primes variant: the set of such pairs is
infinite iff it is unbounded. -/
theorem WeakRuthAaronInfinitude :
    {n : ℕ | IsWeakRuthAaronPair n}.Infinite ↔
      ∀ N : ℕ, ∃ n : ℕ, N < n ∧ IsWeakRuthAaronPair n := by
  rw [Set.infinite_iff_exists_gt]
  exact ⟨fun h N => (h N).imp fun _ hn => ⟨hn.2, hn.1⟩,
    fun h N => (h N).imp fun _ hn => ⟨hn.2, hn.1⟩⟩

end Brockian.RuthAaronPairs

