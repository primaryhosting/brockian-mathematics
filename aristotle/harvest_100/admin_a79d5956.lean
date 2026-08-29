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

/-- `totientIterSum n` is the sum of the iterated totients of `n`:
`φ(n) + φ(φ(n)) + ⋯ + 1`, the iteration stopping once the value `1` is reached.
By convention the sum is `0` for `n ≤ 1`. -/
def totientIterSum : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => Nat.totient (n + 2) + totientIterSum (Nat.totient (n + 2))
  decreasing_by exact Nat.totient_lt _ (by omega)

/-- A *perfect totient number*: a positive integer equal to the sum of its iterated
totients. -/
def PerfectTotient (n : ℕ) : Prop := 0 < n ∧ totientIterSum n = n

lemma totientIterSum_step {n : ℕ} (hn : 2 ≤ n) :
    totientIterSum n = Nat.totient n + totientIterSum (Nat.totient n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [totientIterSum]

lemma totient_two_mul_pow_three (k : ℕ) :
    Nat.totient (2 * 3 ^ (k + 1)) = 2 * 3 ^ k := by
  rw [Nat.totient_mul (Nat.Coprime.pow_right _ (by decide))]
  rw [Nat.totient_prime_pow Nat.prime_three (by omega)]
  simp [Nat.totient_two]

lemma totient_pow_three (k : ℕ) :
    Nat.totient (3 ^ (k + 1)) = 2 * 3 ^ k := by
  rw [Nat.totient_prime_pow Nat.prime_three (by omega)]
  simp

/-- The iterated-totient sum of `2 * 3 ^ k` is `3 ^ k`. -/
lemma totientIterSum_two_mul_pow_three (k : ℕ) :
    totientIterSum (2 * 3 ^ k) = 3 ^ k := by
  induction k with
  | zero => simp [totientIterSum]
  | succ k ih =>
      rw [totientIterSum_step (by
        have : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega)]
      rw [totient_two_mul_pow_three k, ih]
      ring

/-- Every power `3 ^ (k+1)` is a perfect totient number. -/
theorem perfectTotient_pow_three (k : ℕ) : PerfectTotient (3 ^ (k + 1)) := by
  refine ⟨Nat.pos_pow_of_pos _ (by norm_num), ?_⟩
  rw [totientIterSum_step (by
    have : (3:ℕ) ^ 1 ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this)]
  rw [totient_pow_three k, totientIterSum_two_mul_pow_three k]
  ring

/-- **Perfect Totient Infinitude**: there are infinitely many perfect totient numbers. -/
theorem PerfectTotientInfinitude : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ PerfectTotient n := by
  intro N
  refine ⟨3 ^ (N + 1), ?_, perfectTotient_pow_three N⟩
  calc N < N + 1 := Nat.lt_succ_self N
    _ ≤ 3 ^ (N + 1) := Nat.le_of_lt (Nat.lt_pow_self (by norm_num))

/-- The set of perfect totient numbers is infinite. -/
theorem setOf_perfectTotient_infinite : {n : ℕ | PerfectTotient n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨n, hn, hp⟩ := PerfectTotientInfinitude N
  exact absurd (hN hp) (by omega)

end Brockian.PerfectTotient

