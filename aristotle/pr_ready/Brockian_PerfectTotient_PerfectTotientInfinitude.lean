/-!
# Perfect Totient Infinitude
Category: Brockian Conjecture
Target: Brockian.PerfectTotient.PerfectTotientInfinitude
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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


/-!
# Perfect Totient Infinitude
Category: Brockian Conjecture
Target: Brockian.PerfectTotient.PerfectTotientInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede all other commands, so the required
-- header block appears immediately after the single import.)

namespace Brockian.PerfectTotient

/-- `totientSum n` is the sum of the iterated totients
`φ(n) + φ(φ(n)) + ⋯ + 1` of `n` (the iteration stopping when the value `1` is
reached, and that final `1` being included in the sum).  By convention
`totientSum 0 = totientSum 1 = 0`. -/
def totientSum : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => Nat.totient (n + 2) + totientSum (Nat.totient (n + 2))
decreasing_by exact Nat.totient_lt (n + 2) (by omega)

/-- A *perfect totient number* is an integer `n ≥ 2` equal to the sum of its
iterated totients. -/
def IsPerfectTotient (n : ℕ) : Prop := 2 ≤ n ∧ totientSum n = n

lemma totientSum_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    totientSum n = n.totient + totientSum n.totient := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [totientSum]

/-- `φ(2 * 3 ^ (m + 1)) = 2 * 3 ^ m`. -/
lemma totient_two_mul_three_pow_succ (m : ℕ) :
    Nat.totient (2 * 3 ^ (m + 1)) = 2 * 3 ^ m := by
  have hcop : Nat.Coprime 2 (3 ^ (m + 1)) := Nat.Coprime.pow_right _ (by norm_num)
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow (by norm_num) (Nat.succ_pos m)]
  simp [Nat.totient_two]
  ring

lemma totientSum_two_mul_three_pow (m : ℕ) : totientSum (2 * 3 ^ m) = 3 ^ m := by
  induction m with
  | zero =>
      have h1 : totientSum 2 = Nat.totient 2 + totientSum (Nat.totient 2) :=
        totientSum_of_two_le le_rfl
      simp [Nat.totient_two, totientSum] at h1 ⊢
  | succ k ih =>
      have h2 : 2 ≤ 2 * 3 ^ (k + 1) := by
        have : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      rw [totientSum_of_two_le h2, totient_two_mul_three_pow_succ, ih]
      ring

lemma totientSum_three_pow (k : ℕ) : totientSum (3 ^ (k + 1)) = 3 ^ (k + 1) := by
  have h2 : 2 ≤ 3 ^ (k + 1) := by
    calc 2 ≤ 3 ^ 1 := by norm_num
    _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hphi : Nat.totient (3 ^ (k + 1)) = 2 * 3 ^ k := by
    rw [Nat.totient_prime_pow (by norm_num) (Nat.succ_pos k)]
    simp [Nat.mul_comm]
  rw [totientSum_of_two_le h2, hphi, totientSum_two_mul_three_pow]
  ring

/-- Every power `3 ^ (k + 1)` is a perfect totient number. -/
theorem isPerfectTotient_three_pow (k : ℕ) : IsPerfectTotient (3 ^ (k + 1)) := by
  refine ⟨?_, totientSum_three_pow k⟩
  calc 2 ≤ 3 ^ 1 := by norm_num
  _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Infinitude of perfect totient numbers**: there are arbitrarily large
perfect totient numbers. -/
theorem PerfectTotientInfinitude : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ IsPerfectTotient n := by
  intro N
  refine ⟨3 ^ (N + 1), ?_, isPerfectTotient_three_pow N⟩
  calc N < 2 ^ (N + 1) := by
        have := Nat.lt_two_pow_self (n := N)
        omega
  _ ≤ 3 ^ (N + 1) := Nat.pow_le_pow_left (by norm_num) _

end Brockian.PerfectTotient

