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
-- (The header above uses `/- -/` rather than `/-! -/` because a module docstring
-- may not precede the `import` line; the same text is repeated as the module
-- docstring immediately after the import.)

import Mathlib

/-!
# Perfect Totient Infinitude
Category: Brockian Conjecture
Target: Brockian.PerfectTotient.PerfectTotientInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is a *perfect totient number* if the sum of its iterated totients
`φ(n) + φ(φ(n)) + ⋯ + 1` equals `n`. We show there are infinitely many such numbers,
by proving that every power `3 ^ (k + 1)` is a perfect totient number.
-/

namespace Brockian
namespace PerfectTotient

/-- `totientSum n` is the sum of the iterated totients of `n`:
`φ(n) + φ(φ(n)) + ⋯ + 1`, the iteration stopping when the value `1` is reached
(the final `1` is included). By convention `totientSum 0 = totientSum 1 = 0`. -/
def totientSum : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => Nat.totient (n + 2) + totientSum (Nat.totient (n + 2))
  decreasing_by exact Nat.totient_lt _ (by omega)

/-- A natural number `n` is a *perfect totient number* when the sum of its iterated
totients equals `n` itself. -/
def IsPerfectTotient (n : ℕ) : Prop := totientSum n = n

lemma totientSum_one : totientSum 1 = 0 := by rw [totientSum]

lemma totientSum_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    totientSum n = Nat.totient n + totientSum (Nat.totient n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [totientSum]

lemma totientSum_two : totientSum 2 = 1 := by
  rw [totientSum_of_two_le le_rfl, Nat.totient_two, totientSum_one]

lemma totient_two_mul_three_pow (m : ℕ) :
    Nat.totient (2 * 3 ^ (m + 1)) = 2 * 3 ^ m := by
  rw [Nat.totient_mul (Nat.Coprime.pow_right _ (by norm_num)),
    Nat.totient_prime_pow (by norm_num) (Nat.succ_pos m)]
  simp [Nat.totient_two]
  ring

/-- The iterated totient sum of `2 * 3 ^ m` is `3 ^ m`. -/
lemma totientSum_two_mul_three_pow (m : ℕ) : totientSum (2 * 3 ^ m) = 3 ^ m := by
  induction m with
  | zero => simpa using totientSum_two
  | succ m ih =>
      have h1 : 1 ≤ 3 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
      rw [totientSum_of_two_le (by omega), totient_two_mul_three_pow, ih]
      ring

/-- Every power `3 ^ (k + 1)` is a perfect totient number. -/
theorem isPerfectTotient_three_pow (k : ℕ) : IsPerfectTotient (3 ^ (k + 1)) := by
  have h2 : 2 ≤ 3 ^ (k + 1) := by
    calc 2 ≤ 3 ^ 1 := by norm_num
    _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hphi : Nat.totient (3 ^ (k + 1)) = 2 * 3 ^ k := by
    rw [Nat.totient_prime_pow (by norm_num) (Nat.succ_pos k)]
    simp [Nat.mul_comm]
  rw [IsPerfectTotient, totientSum_of_two_le h2, hphi, totientSum_two_mul_three_pow]
  ring

/-- **Perfect Totient Infinitude**: there are infinitely many perfect totient numbers. -/
theorem PerfectTotientInfinitude : {n : ℕ | IsPerfectTotient n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨3 ^ (a + 1), isPerfectTotient_three_pow a, ?_⟩
  calc a < a + 1 := Nat.lt_succ_self a
    _ ≤ 3 ^ (a + 1) := Nat.le_of_lt (Nat.lt_pow_self (by norm_num))

end PerfectTotient
end Brockian

