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
# Perfect Totient Infinitude
Category: Brockian Conjecture
Target: Brockian.PerfectTotient.PerfectTotientInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PerfectTotient

open Nat

/-- `totientSum n` is the sum of the iterated totients
`φ n + φ (φ n) + φ (φ (φ n)) + ⋯`, continued until the value `1` is reached
(the final `1` being included in the sum).  By convention it is `0` for `n ≤ 1`. -/
def totientSum : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => Nat.totient (n + 2) + totientSum (Nat.totient (n + 2))
  decreasing_by exact Nat.totient_lt _ (by omega)

/-- A *perfect totient number* is a number equal to the sum of its iterated totients. -/
def IsPerfectTotient (n : ℕ) : Prop := 2 ≤ n ∧ totientSum n = n

theorem totientSum_succ_succ (n : ℕ) :
    totientSum (n + 2) = Nat.totient (n + 2) + totientSum (Nat.totient (n + 2)) := by
  rw [totientSum]

theorem totientSum_eq (n : ℕ) (hn : 2 ≤ n) :
    totientSum n = Nat.totient n + totientSum (Nat.totient n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact totientSum_succ_succ m

theorem totient_two_mul_pow_three (j : ℕ) :
    Nat.totient (2 * 3 ^ (j + 1)) = 2 * 3 ^ j := by
  rw [Nat.totient_mul (Nat.Coprime.pow_right (j + 1) (by norm_num : Nat.Coprime 2 3))]
  rw [Nat.totient_prime_pow (by norm_num) (Nat.succ_pos j)]
  simp [Nat.totient_two, Nat.mul_comm]

theorem totient_pow_three (k : ℕ) :
    Nat.totient (3 ^ (k + 1)) = 2 * 3 ^ k := by
  rw [Nat.totient_prime_pow (by norm_num) (Nat.succ_pos k)]
  simp [Nat.mul_comm]

/-- The sum of the iterated totients of `2 * 3 ^ j` is `3 ^ j`. -/
theorem totientSum_two_mul_pow_three (j : ℕ) : totientSum (2 * 3 ^ j) = 3 ^ j := by
  induction j with
  | zero =>
      show totientSum 2 = 1
      rw [totientSum_succ_succ 0]
      norm_num [Nat.totient_two, totientSum]
  | succ j ih =>
      have h2 : 2 ≤ 2 * 3 ^ (j + 1) := by
        have : 1 ≤ 3 ^ (j + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      rw [totientSum_eq _ h2, totient_two_mul_pow_three, ih]
      ring

/-- Every power `3 ^ (k+1)` is a perfect totient number. -/
theorem totientSum_pow_three (k : ℕ) : totientSum (3 ^ (k + 1)) = 3 ^ (k + 1) := by
  have h2 : 2 ≤ 3 ^ (k + 1) := by
    calc 2 ≤ 3 ^ 1 := by norm_num
    _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [totientSum_eq _ h2, totient_pow_three, totientSum_two_mul_pow_three]
  ring

theorem isPerfectTotient_pow_three (k : ℕ) : IsPerfectTotient (3 ^ (k + 1)) := by
  refine ⟨?_, totientSum_pow_three k⟩
  calc 2 ≤ 3 ^ 1 := by norm_num
  _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Perfect Totient Infinitude**: there are arbitrarily large perfect totient numbers,
i.e. numbers equal to the sum of their iterated totients. -/
theorem PerfectTotientInfinitude : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ IsPerfectTotient n := by
  intro N
  refine ⟨3 ^ (N + 1), ?_, isPerfectTotient_pow_three N⟩
  calc N < N + 1 := Nat.lt_succ_self N
  _ ≤ 3 ^ (N + 1) := Nat.le_of_lt (Nat.lt_pow_self (by norm_num))

/-- The set of perfect totient numbers is infinite. -/
theorem setOf_isPerfectTotient_infinite : {n : ℕ | IsPerfectTotient n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨n, hn, hp⟩ := PerfectTotientInfinitude B
  exact absurd (hB hp) (by omega)

end Brockian.PerfectTotient

