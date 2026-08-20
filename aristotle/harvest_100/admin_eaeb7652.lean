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

namespace Brockian.PerfectTotient

open Nat

/-- `totientSum n` is the sum of the iterated totients
`φ(n) + φ(φ(n)) + ⋯ + 1` of `n`, the iteration stopping once the value `1` is
reached (and `1` being the final summand).  By convention it is `0` for `n ≤ 1`. -/
def totientSum : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => Nat.totient (n + 2) + totientSum (Nat.totient (n + 2))
  decreasing_by exact Nat.totient_lt _ (by omega)

/-- A natural number `n` is a *perfect totient number* when it is positive and equals
the sum of its iterated totients `φ(n) + φ(φ(n)) + ⋯ + 1`. -/
def IsPerfectTotient (n : ℕ) : Prop := 0 < n ∧ totientSum n = n

lemma totientSum_zero : totientSum 0 = 0 := by rw [totientSum]

lemma totientSum_one : totientSum 1 = 0 := by rw [totientSum]

/-- The defining recursion for `totientSum`, for `n ≥ 2`. -/
lemma totientSum_eq (n : ℕ) (hn : 2 ≤ n) :
    totientSum n = Nat.totient n + totientSum (Nat.totient n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [totientSum]

lemma totientSum_two : totientSum 2 = 1 := by
  rw [totientSum_eq 2 le_rfl]
  simp [totientSum_one]

/-- `φ(2 · 3^(m+1)) = 2 · 3^m`. -/
lemma totient_two_mul_three_pow_succ (m : ℕ) :
    Nat.totient (2 * 3 ^ (m + 1)) = 2 * 3 ^ m := by
  have hcop : Nat.Coprime 2 (3 ^ (m + 1)) := Nat.Coprime.pow_right _ (by decide)
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow (by norm_num) (Nat.succ_pos m)]
  simp [Nat.totient_two, Nat.mul_comm]

/-- Key computation: the iterated-totient sum of `2 · 3^m` is `3^m`. -/
lemma totientSum_two_mul_three_pow (m : ℕ) : totientSum (2 * 3 ^ m) = 3 ^ m := by
  induction m with
  | zero => simpa using totientSum_two
  | succ m ih =>
      have h2 : 2 ≤ 2 * 3 ^ (m + 1) := by
        have : 1 ≤ 3 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      rw [totientSum_eq _ h2, totient_two_mul_three_pow_succ m, ih]
      ring

/-- Every power `3^(k+1)` is a perfect totient number. -/
theorem totientSum_three_pow_succ (k : ℕ) : totientSum (3 ^ (k + 1)) = 3 ^ (k + 1) := by
  have h2 : 2 ≤ 3 ^ (k + 1) := by
    calc 2 ≤ 3 ^ 1 := by norm_num
    _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hphi : Nat.totient (3 ^ (k + 1)) = 2 * 3 ^ k := by
    rw [Nat.totient_prime_pow (by norm_num) (Nat.succ_pos k)]
    simp [Nat.mul_comm]
  rw [totientSum_eq _ h2, hphi, totientSum_two_mul_three_pow k]
  ring

theorem isPerfectTotient_three_pow_succ (k : ℕ) : IsPerfectTotient (3 ^ (k + 1)) :=
  ⟨pow_pos (by norm_num) _, totientSum_three_pow_succ k⟩

/-- **Perfect Totient Infinitude.** There are infinitely many perfect totient numbers,
i.e. numbers `n > 0` with `n = φ(n) + φ(φ(n)) + ⋯ + 1`. -/
theorem PerfectTotientInfinitude : {n : ℕ | IsPerfectTotient n}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 3 ^ (k + 1)) ?_ ?_
  · intro a b hab
    simpa using Nat.pow_right_injective (by norm_num) hab
  · intro k
    exact isPerfectTotient_three_pow_succ k

end Brockian.PerfectTotient

