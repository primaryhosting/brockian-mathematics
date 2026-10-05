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

namespace Brockian
namespace PerfectTotient

open Nat

/-- `totientSum n` is the sum of the iterated totients of `n`:
`φ(n) + φ(φ(n)) + ⋯ + 1` (and `0` for `n ≤ 1`). -/
def totientSum : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => Nat.totient (n + 2) + totientSum (Nat.totient (n + 2))
  decreasing_by exact Nat.totient_lt (n + 2) (by omega)

/-- A *perfect totient number* is a positive `n` equal to the sum of its iterated totients. -/
def IsPerfectTotient (n : ℕ) : Prop := 0 < n ∧ totientSum n = n

lemma totientSum_eq (n : ℕ) (hn : 2 ≤ n) :
    totientSum n = Nat.totient n + totientSum (Nat.totient n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [totientSum]

@[simp] lemma totientSum_one : totientSum 1 = 0 := by rw [totientSum]

lemma totient_three_pow (j : ℕ) : Nat.totient (3 ^ (j + 1)) = 2 * 3 ^ j := by
  rw [Nat.totient_prime_pow (by norm_num) (Nat.succ_pos j)]
  simp [Nat.mul_comm]

lemma totient_two_mul_three_pow (j : ℕ) :
    Nat.totient (2 * 3 ^ (j + 1)) = 2 * 3 ^ j := by
  rw [Nat.totient_mul (by
    simpa using (Nat.Coprime.pow_right (j + 1) (by norm_num : Nat.Coprime 2 3)))]
  rw [totient_three_pow j]
  simp

/-- The iterated totient sum of `2 * 3 ^ j` is `3 ^ j`. -/
lemma totientSum_two_mul_three_pow (j : ℕ) : totientSum (2 * 3 ^ j) = 3 ^ j := by
  induction j with
  | zero => rw [pow_zero, Nat.mul_one, totientSum_eq 2 le_rfl]; simp
  | succ j ih =>
      have h2 : 2 ≤ 2 * 3 ^ (j + 1) := by
        have : 1 ≤ 3 ^ (j + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      rw [totientSum_eq _ h2, totient_two_mul_three_pow j, ih]
      ring

/-- Every power `3 ^ (k + 1)` is a perfect totient number. -/
lemma totientSum_three_pow (k : ℕ) : totientSum (3 ^ (k + 1)) = 3 ^ (k + 1) := by
  have h2 : 2 ≤ 3 ^ (k + 1) := by
    calc 2 ≤ 3 ^ 1 := by norm_num
    _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [totientSum_eq _ h2, totient_three_pow k, totientSum_two_mul_three_pow k]
  ring

lemma isPerfectTotient_three_pow (k : ℕ) : IsPerfectTotient (3 ^ (k + 1)) :=
  ⟨Nat.pow_pos (by norm_num), totientSum_three_pow k⟩

/-- **Infinitude of perfect totient numbers**: for every `N` there is a perfect totient
number exceeding `N`. -/
theorem PerfectTotientInfinitude : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ IsPerfectTotient n := by
  intro N
  refine ⟨3 ^ (N + 1), ?_, isPerfectTotient_three_pow N⟩
  have h := Nat.lt_pow_self (n := N + 1) (a := 3) (by norm_num)
  omega

/-- The set of perfect totient numbers is infinite. -/
theorem setOf_isPerfectTotient_infinite : {n : ℕ | IsPerfectTotient n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨n, hn, hp⟩ := PerfectTotientInfinitude N
  exact absurd (hN hp) (by omega)

end PerfectTotient
end Brockian

