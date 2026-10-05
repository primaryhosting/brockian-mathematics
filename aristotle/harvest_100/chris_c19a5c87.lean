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

Infinitely many perfect totient numbers: every power `3 ^ (k+1)` is one.
-/

namespace Brockian.PerfectTotient

/-- `totientIterSum n` is the sum of the iterated totients of `n`, i.e.
`φ(n) + φ(φ(n)) + φ(φ(φ(n))) + ⋯`, the iteration stopping once the value `1` is reached
(the terminal `1` is included in the sum, as is standard). -/
def totientIterSum : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => Nat.totient (n + 2) + totientIterSum (Nat.totient (n + 2))
  decreasing_by exact Nat.totient_lt (n + 2) (by omega)

/-- A *perfect totient number* is a positive integer equal to the sum of its iterated
totients. -/
def IsPerfectTotient (n : ℕ) : Prop := 0 < n ∧ totientIterSum n = n

/-- Unfolding lemma for `totientIterSum` at arguments `≥ 2`. -/
lemma totientIterSum_eq (n : ℕ) (hn : 2 ≤ n) :
    totientIterSum n = Nat.totient n + totientIterSum (Nat.totient n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [totientIterSum]

lemma totient_three_pow (k : ℕ) : Nat.totient (3 ^ (k + 1)) = 2 * 3 ^ k := by
  rw [Nat.totient_prime_pow (by norm_num) (Nat.succ_pos k)]
  simp [Nat.mul_comm]

lemma totient_two_mul_three_pow (k : ℕ) :
    Nat.totient (2 * 3 ^ (k + 1)) = 2 * 3 ^ k := by
  rw [Nat.totient_mul (by
      simp [Nat.Coprime, Nat.coprime_pow_right_iff (Nat.succ_pos k)])]
  rw [totient_three_pow k, Nat.totient_two, one_mul]

/-- The iterated totient sum of `2 * 3 ^ k` is `3 ^ k`. -/
lemma totientIterSum_two_mul_three_pow (k : ℕ) : totientIterSum (2 * 3 ^ k) = 3 ^ k := by
  induction k with
  | zero => simp [totientIterSum_eq 2 (by norm_num), totientIterSum]
  | succ k ih =>
      have h1 : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
      rw [totientIterSum_eq _ (by omega), totient_two_mul_three_pow k, ih]
      ring

/-- Every power `3 ^ (k + 1)` has iterated totient sum equal to itself. -/
lemma totientIterSum_three_pow (k : ℕ) : totientIterSum (3 ^ (k + 1)) = 3 ^ (k + 1) := by
  have h2 : 2 ≤ 3 ^ (k + 1) := by
    have : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    calc 2 ≤ 3 * 1 := by norm_num
      _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_left 3 this
      _ = 3 ^ (k + 1) := by ring
  rw [totientIterSum_eq _ h2, totient_three_pow k, totientIterSum_two_mul_three_pow k]
  ring

lemma isPerfectTotient_three_pow (k : ℕ) : IsPerfectTotient (3 ^ (k + 1)) :=
  ⟨by positivity, totientIterSum_three_pow k⟩

/-- **Perfect Totient Infinitude**: there are infinitely many perfect totient numbers. -/
theorem PerfectTotientInfinitude : {n : ℕ | IsPerfectTotient n}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 3 ^ (k + 1))
  · intro a b hab
    have := Nat.pow_right_injective (by norm_num) hab
    omega
  · intro k
    exact isPerfectTotient_three_pow k

end Brockian.PerfectTotient

