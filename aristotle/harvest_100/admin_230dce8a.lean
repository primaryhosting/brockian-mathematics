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
-- (The header above uses `/-` rather than `/-!` because Lean does not allow a module
-- docstring to precede the `import` commands; the text is otherwise verbatim.)

import Mathlib

/-!
# Landau Fourth Conjecture

Landau's fourth problem asks whether there are infinitely many primes of the form `n ^ 2 + 1`.
This is a well-known open problem, so what is proved here is:

* `LandauFourthConjecture` : a **conditional** reduction — Bunyakovsky's conjecture
  (in the form `BunyakovskyHypothesis`) implies Landau's fourth conjecture
  (`LandauFourthStatement`).  All the hypotheses of Bunyakovsky's conjecture are verified
  unconditionally for the polynomial `X ^ 2 + 1`.
* `X_sq_add_one_irreducible` : `X ^ 2 + 1` is irreducible over `ℤ`.
* `infinite_setOf_prime_dvd_sq_add_one` : an **unconditional** partial result — infinitely many
  primes divide some number of the form `n ^ 2 + 1`.
* `infinite_setOf_large_prime_factor` : an **unconditional** partial result — for infinitely many
  `n`, the number `n ^ 2 + 1` has a prime factor exceeding `2 * n`.
-/

open Polynomial

namespace Brockian.LandauNSquaredPlusOne

/-- **Landau's fourth conjecture**: there are infinitely many natural numbers `n` such that
`n ^ 2 + 1` is prime. -/
def LandauFourthStatement : Prop := {n : ℕ | Nat.Prime (n ^ 2 + 1)}.Infinite

/-- **Bunyakovsky's conjecture**: if `f : ℤ[X]` has positive degree and positive leading
coefficient, is irreducible over `ℤ`, and has no fixed prime divisor (for every prime `p` there
is some natural number `n` with `p ∤ f n`), then `f` takes prime values at infinitely many
natural numbers. -/
def BunyakovskyHypothesis : Prop :=
  ∀ f : ℤ[X], 0 < f.natDegree → 0 < f.leadingCoeff → Irreducible f →
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ¬ ((p : ℤ) ∣ f.eval (n : ℤ))) →
    {n : ℕ | Prime (f.eval (n : ℤ))}.Infinite

/-- `X ^ 2 + 1` is monic. -/
theorem X_sq_add_one_monic : (X ^ 2 + 1 : ℤ[X]).Monic := by
  apply Polynomial.monic_X_pow_add (n := 2)
  simp

/-- `X ^ 2 + 1` has degree `2`. -/
theorem X_sq_add_one_natDegree : (X ^ 2 + 1 : ℤ[X]).natDegree = 2 := by
  compute_degree!

/-- `X ^ 2 + 1` is irreducible over `ℤ`. -/
theorem X_sq_add_one_irreducible : Irreducible (X ^ 2 + 1 : ℤ[X]) := by
  rw [X_sq_add_one_monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)]
  have hmap : ((X ^ 2 + 1 : ℤ[X]).map (algebraMap ℤ ℚ)) = (X ^ 2 + 1 : ℚ[X]) := by simp
  rw [hmap]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have h : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree!
    simp [h]
  · intro x hx
    simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one] at hx
    nlinarith [sq_nonneg x]

/-- The polynomial `X ^ 2 + 1` has no fixed prime divisor: indeed its value at `0` is `1`. -/
theorem X_sq_add_one_no_fixed_divisor (p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, ¬ ((p : ℤ) ∣ (X ^ 2 + 1 : ℤ[X]).eval (n : ℤ)) := by
  refine ⟨0, fun h => ?_⟩
  simp only [Nat.cast_zero, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one] at h
  rw [show ((0 : ℤ) ^ 2 + 1) = ((1 : ℕ) : ℤ) by norm_num, Int.natCast_dvd_natCast] at h
  exact hp.one_lt.ne' (Nat.dvd_one.mp h)

/-- The values of `X ^ 2 + 1` at natural numbers are exactly the numbers `n ^ 2 + 1`, and
primality over `ℤ` matches primality over `ℕ`. -/
theorem setOf_prime_eval_eq :
    {n : ℕ | Prime ((X ^ 2 + 1 : ℤ[X]).eval (n : ℤ))} = {n : ℕ | Nat.Prime (n ^ 2 + 1)} := by
  ext n
  simp only [Set.mem_setOf_eq, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one]
  rw [show ((n : ℤ) ^ 2 + 1) = ((n ^ 2 + 1 : ℕ) : ℤ) by push_cast; ring,
    ← Nat.prime_iff_prime_int]

/-- **Conditional reduction of Landau's fourth conjecture.**  Bunyakovsky's conjecture implies
that there are infinitely many primes of the form `n ^ 2 + 1`. -/
theorem LandauFourthConjecture (hB : BunyakovskyHypothesis) : LandauFourthStatement := by
  have h := hB (X ^ 2 + 1) (by rw [X_sq_add_one_natDegree]; norm_num)
    (by rw [X_sq_add_one_monic.leadingCoeff]; norm_num)
    X_sq_add_one_irreducible X_sq_add_one_no_fixed_divisor
  rwa [setOf_prime_eval_eq] at h

/-- **Unconditional partial result.**  There are infinitely many primes `p` dividing some number
of the form `n ^ 2 + 1`; equivalently, infinitely many primes occur as prime factors of the
sequence `n ^ 2 + 1`. -/
theorem infinite_setOf_prime_dvd_sq_add_one :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p ∣ n ^ 2 + 1}.Infinite := by
  refine Set.Infinite.mono ?_
    (Nat.infinite_setOf_prime_and_eq_mod (q := 4) (a := 1) isUnit_one)
  rintro p ⟨hp, hp4⟩
  refine ⟨hp, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod : p % 4 = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' p 1 4).mp (by simpa using hp4)
    simpa using this
  obtain ⟨r, hr⟩ : IsSquare (-1 : ZMod p) := by
    rw [ZMod.exists_sq_eq_neg_one_iff]
    omega
  refine ⟨r.val, ?_⟩
  have hz : ((r.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rw [sq, ← hr]; ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp hz

/-- Auxiliary criterion: if `m ^ 2 + 1` vanishes modulo `p`, then `p ∣ m ^ 2 + 1`. -/
theorem dvd_sq_add_one_of_cast_eq_zero (p m : ℕ) (h : ((m : ZMod p)) ^ 2 + 1 = 0) :
    p ∣ m ^ 2 + 1 :=
  (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast; exact h)

/-- **Unconditional partial result towards Landau's fourth conjecture.**  There are infinitely
many `n` for which `n ^ 2 + 1` has a prime factor larger than `2 * n`; in particular `n ^ 2 + 1`
has a prime factor of size comparable to `n ^ 2` infinitely often.  (Landau's conjecture is the
statement that `n ^ 2 + 1` is itself prime infinitely often.) -/
theorem infinite_setOf_large_prime_factor :
    {n : ℕ | ∃ p : ℕ, p.Prime ∧ p ∣ n ^ 2 + 1 ∧ 2 * n < p}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨p, hpgt, hp, hp4⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4) (a := 1) isUnit_one ((N + 1) ^ 2 + 1)
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod : p % 4 = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' p 1 4).mp (by simpa using hp4)
    simpa using this
  obtain ⟨r, hr⟩ : IsSquare (-1 : ZMod p) := by
    rw [ZMod.exists_sq_eq_neg_one_iff]; omega
  have hrsq : (r : ZMod p) ^ 2 + 1 = 0 := by rw [sq, ← hr]; ring
  have hrval : r.val < p := ZMod.val_lt r
  have hcast : ((r.val : ℕ) : ZMod p) = r := ZMod.natCast_val r |>.trans (ZMod.cast_id _ _)
  have hd1 : p ∣ r.val ^ 2 + 1 :=
    dvd_sq_add_one_of_cast_eq_zero p r.val (by rw [hcast]; exact hrsq)
  have hd2 : p ∣ (p - r.val) ^ 2 + 1 := by
    refine dvd_sq_add_one_of_cast_eq_zero p _ ?_
    have hc : ((p - r.val : ℕ) : ZMod p) = -r := by
      rw [Nat.cast_sub hrval.le, hcast]; simp
    rw [hc, neg_pow]
    simpa using hrsq
  have hr0 : r.val ≠ 0 := by
    intro h
    have hz : (r : ZMod p) = 0 := by rw [← hcast, h]; simp
    rw [hz] at hrsq
    simp at hrsq
  set m := min r.val (p - r.val) with hm
  have hpodd : p % 2 = 1 := by omega
  have h2m : 2 * m < p := by
    rcases le_total r.val (p - r.val) with h | h
    · have hmm : m = r.val := by simp [hm, h]
      omega
    · have hmm : m = p - r.val := by simp [hm, h]
      omega
  have hdm : p ∣ m ^ 2 + 1 := by
    rcases le_total r.val (p - r.val) with h | h
    · have hmm : m = r.val := by simp [hm, h]
      rw [hmm]; exact hd1
    · have hmm : m = p - r.val := by simp [hm, h]
      rw [hmm]; exact hd2
  have hge : p ≤ m ^ 2 + 1 := Nat.le_of_dvd (by positivity) hdm
  refine ⟨m, ⟨p, hp, hdm, h2m⟩, ?_⟩
  nlinarith [hge, hpgt]

/-- A convenient reformulation of Landau's fourth conjecture. -/
theorem landauFourthStatement_iff :
    LandauFourthStatement ↔ ∀ N : ℕ, ∃ n > N, Nat.Prime (n ^ 2 + 1) := by
  constructor
  · intro h N
    obtain ⟨n, hn, hnN⟩ := Set.infinite_iff_exists_gt.mp h N
    exact ⟨n, hnN, hn⟩
  · intro h
    rw [LandauFourthStatement, Set.infinite_iff_exists_gt]
    intro N
    obtain ⟨n, hnN, hn⟩ := h N
    exact ⟨n, hn, hnN⟩

end Brockian.LandauNSquaredPlusOne

