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
# Perfect Totient Infinitude
Category: Brockian Conjecture
Target: Brockian.PerfectTotient.PerfectTotientInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Perfect Totient Infinitude
Category: Brockian Conjecture
Target: Brockian.PerfectTotient.PerfectTotientInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PerfectTotient

/-- `totientSum n` is the sum of the iterated totients of `n`, i.e.
`φ(n) + φ(φ(n)) + ⋯ + 1`, where the iteration stops once the value `1` is reached
(`totientSum 1 = 0`, `totientSum 0 = 0`). -/
def totientSum (n : ℕ) : ℕ :=
  if _h : 2 ≤ n then Nat.totient n + totientSum (Nat.totient n) else 0
termination_by n
decreasing_by exact Nat.totient_lt n _h

/-- A *perfect totient number* is an integer `n ≥ 2` equal to the sum of its
iterated totients. -/
def IsPerfectTotient (n : ℕ) : Prop := 2 ≤ n ∧ totientSum n = n

lemma totientSum_of_two_le {n : ℕ} (h : 2 ≤ n) :
    totientSum n = Nat.totient n + totientSum (Nat.totient n) := by
  rw [totientSum]; simp [h]

lemma totientSum_one : totientSum 1 = 0 := by
  rw [totientSum]; norm_num

lemma totientSum_two : totientSum 2 = 1 := by
  rw [totientSum_of_two_le (le_refl 2), Nat.totient_two, totientSum_one]

/-- `φ(3 ^ (k + 1)) = 2 * 3 ^ k`. -/
lemma totient_three_pow_succ (k : ℕ) : Nat.totient (3 ^ (k + 1)) = 2 * 3 ^ k := by
  rw [Nat.totient_prime_pow (by norm_num) (Nat.succ_pos k), Nat.succ_sub_one]
  ring

/-- `φ(2 * 3 ^ (k + 1)) = 2 * 3 ^ k`. -/
lemma totient_two_mul_three_pow_succ (k : ℕ) :
    Nat.totient (2 * 3 ^ (k + 1)) = 2 * 3 ^ k := by
  rw [Nat.totient_mul (by
      simpa using (Nat.Coprime.pow_right (k + 1) (by norm_num : Nat.Coprime 2 3)))]
  rw [totient_three_pow_succ, Nat.totient_two, one_mul]

/-- The iterated totient sum of `2 * 3 ^ k` is `3 ^ k`. -/
lemma totientSum_two_mul_three_pow (k : ℕ) : totientSum (2 * 3 ^ k) = 3 ^ k := by
  induction k with
  | zero => simpa using totientSum_two
  | succ k ih =>
      have h2 : 2 ≤ 2 * 3 ^ (k + 1) := by
        have : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      rw [totientSum_of_two_le h2, totient_two_mul_three_pow_succ, ih]
      ring

/-- Every power `3 ^ (k + 1)` is a perfect totient number. -/
lemma totientSum_three_pow_succ (k : ℕ) : totientSum (3 ^ (k + 1)) = 3 ^ (k + 1) := by
  have h2 : 2 ≤ 3 ^ (k + 1) := by
    have h1 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    calc 2 ≤ 3 * 1 := by norm_num
      _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_left 3 h1
      _ = 3 ^ (k + 1) := by ring
  rw [totientSum_of_two_le h2, totient_three_pow_succ, totientSum_two_mul_three_pow]
  ring

lemma isPerfectTotient_three_pow_succ (k : ℕ) : IsPerfectTotient (3 ^ (k + 1)) := by
  refine ⟨?_, totientSum_three_pow_succ k⟩
  have h1 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
  calc 2 ≤ 3 * 1 := by norm_num
    _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_left 3 h1
    _ = 3 ^ (k + 1) := by ring

/-- **Perfect Totient Infinitude**: there are infinitely many perfect totient numbers. -/
theorem PerfectTotientInfinitude : {n : ℕ | IsPerfectTotient n}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => 3 ^ (k + 1)) ?_ (fun k => isPerfectTotient_three_pow_succ k)
  intro a b hab
  have := Nat.pow_right_injective (by norm_num) hab
  omega

/-- Restatement: for every `N` there is a perfect totient number exceeding `N`. -/
theorem exists_perfectTotient_gt (N : ℕ) : ∃ n, N < n ∧ IsPerfectTotient n := by
  obtain ⟨n, hn, hgt⟩ := PerfectTotientInfinitude.exists_gt N
  exact ⟨n, hgt, hn⟩

end Brockian.PerfectTotient

#print axioms Brockian.PerfectTotient.PerfectTotientInfinitude

