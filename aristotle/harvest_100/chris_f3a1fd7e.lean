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

A *perfect totient number* is a positive integer `n` equal to the sum of its iterated
totients `φ n + φ (φ n) + ⋯ + 1`.  We show that the set of such numbers is infinite,
by proving that every power `3 ^ (k+1)` is a perfect totient number.
-/

namespace Brockian.PerfectTotient

/-- `totientSum n` is the sum of the iterated totients of `n`:
`φ n + φ (φ n) + ⋯ + 1`, the iteration stopping once the value reaches `1`. -/
def totientSum (n : ℕ) : ℕ :=
  if 1 < n then n.totient + totientSum n.totient else 0
decreasing_by exact Nat.totient_lt n (by assumption)

/-- Unfolding lemma for `totientSum`. -/
lemma totientSum_eq (n : ℕ) (h : 1 < n) :
    totientSum n = n.totient + totientSum n.totient := by
  rw [totientSum]
  simp [h]

@[simp] lemma totientSum_one : totientSum 1 = 0 := by
  rw [totientSum]
  simp

/-- A natural number `n` is a *perfect totient number* when the sum of its iterated
totients equals `n` itself. -/
def IsPerfectTotient (n : ℕ) : Prop := 0 < n ∧ totientSum n = n

lemma totient_two_mul_three_pow (k : ℕ) :
    Nat.totient (2 * 3 ^ (k + 1)) = 2 * 3 ^ k := by
  rw [Nat.totient_mul (Nat.Coprime.pow_right _ (show Nat.Coprime 2 3 by decide)),
    Nat.totient_prime_pow (by norm_num) (Nat.succ_pos k)]
  simp only [Nat.totient_two, one_mul, Nat.succ_sub_one]
  ring

/-- The iterated totient sum of `2 * 3 ^ k` is `3 ^ k`. -/
lemma totientSum_two_mul_three_pow (k : ℕ) : totientSum (2 * 3 ^ k) = 3 ^ k := by
  induction k with
  | zero =>
      show totientSum 2 = 1
      rw [totientSum_eq _ (by norm_num), Nat.totient_two, totientSum_one]
  | succ k ih =>
      have h1 : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
      rw [totientSum_eq _ (by omega), totient_two_mul_three_pow, ih]
      ring

/-- Every power `3 ^ (k+1)` has iterated totient sum equal to itself. -/
lemma totientSum_three_pow_succ (k : ℕ) : totientSum (3 ^ (k + 1)) = 3 ^ (k + 1) := by
  have h : (1 : ℕ) < 3 ^ (k + 1) := by
    calc (1:ℕ) < 3 ^ 1 := by norm_num
    _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [totientSum_eq _ h, Nat.totient_prime_pow (by norm_num) (Nat.succ_pos k),
    show 3 ^ (k + 1 - 1) * (3 - 1) = 2 * 3 ^ k by simp only [Nat.add_sub_cancel]; ring,
    totientSum_two_mul_three_pow]
  ring

/-- Every power `3 ^ (k+1)` is a perfect totient number. -/
lemma isPerfectTotient_three_pow_succ (k : ℕ) : IsPerfectTotient (3 ^ (k + 1)) :=
  ⟨Nat.pow_pos (by norm_num), totientSum_three_pow_succ k⟩

/-- **Perfect Totient Infinitude**: there are infinitely many perfect totient numbers.
Indeed, the set of perfect totient numbers contains every power `3 ^ (k+1)`. -/
theorem PerfectTotientInfinitude : {n : ℕ | IsPerfectTotient n}.Infinite := by
  apply Set.Infinite.mono (s := (fun k : ℕ => 3 ^ (k + 1)) '' Set.univ)
  · rintro _ ⟨k, -, rfl⟩
    exact isPerfectTotient_three_pow_succ k
  · apply Set.Infinite.image
    · exact Set.injOn_of_injective fun a b hab => by
        have := Nat.pow_right_injective (by norm_num) hab
        omega
    · exact Set.infinite_univ

/-- Equivalent phrasing: perfect totient numbers exceed every bound. -/
theorem exists_perfectTotient_gt (N : ℕ) : ∃ n, N < n ∧ IsPerfectTotient n := by
  obtain ⟨n, hn, hgt⟩ := PerfectTotientInfinitude.exists_gt N
  exact ⟨n, hgt, hn⟩

end Brockian.PerfectTotient

