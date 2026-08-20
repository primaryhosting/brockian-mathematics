import Mathlib
/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the very first command in a file, so the header
comment appears immediately after it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace QPhys

open Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The degree-`N` homogeneous component of the product `exp a * exp b`. -/

lemma bchCoef_rec (N j : ℕ) :
    ((N + 2 : ℕ) : ℚ) * bchCoef (N + 2) j
      = bchCoef (N + 1) j + (if j = 0 then 0 else bchCoef N (j - 1)) := by
  cases j with
  | zero =>
    simp only [bchCoef, Nat.mul_zero, Nat.zero_le, if_pos, Nat.sub_zero,
      Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one]
    rw [Nat.factorial_succ (N + 1)]
    push_cast
    have h1 : ((N + 1)! : ℚ) ≠ 0 := by positivity
    field_simp
    ring
  | succ k =>
    have hk0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
    simp only [hk0, if_false, Nat.add_sub_cancel]
    have hfk : ((k ! : ℚ)) ≠ 0 := by positivity
    rcases le_or_gt (2 * (k + 1)) (N + 1) with h | h
    · have h2 : 2 * (k + 1) ≤ N + 2 := by omega
      have h3 : 2 * k ≤ N := by omega
      obtain ⟨v, hv⟩ : ∃ v, N - 2 * k = v + 1 := ⟨N - 2 * k - 1, by omega⟩
      have e1 : N + 2 - 2 * (k + 1) = v + 1 := by omega
      have e2 : N + 1 - 2 * (k + 1) = v := by omega
      rw [bchCoef, bchCoef, bchCoef, if_pos h2, if_pos h, if_pos h3, e1, e2, hv]
      have hNv : ((N + 2 : ℕ) : ℚ) = ((v : ℚ) + 1) + 2 * ((k : ℚ) + 1) := by
        have hN : N + 2 = (v + 1) + 2 * (k + 1) := by omega
        rw [hN]; push_cast; ring
      have hfv : ((v ! : ℚ)) ≠ 0 := by positivity
      rw [hNv]
      simp only [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · rcases eq_or_lt_of_le (show N + 2 ≤ 2 * (k + 1) by omega) with h4 | h4
      · have h3 : 2 * k ≤ N := by omega
        have h5 : ¬ (2 * (k + 1) ≤ N + 1) := by omega
        have h6 : N + 2 - 2 * (k + 1) = 0 := by omega
        have h7 : N - 2 * k = 0 := by omega
        rw [bchCoef, bchCoef, bchCoef, if_pos (by omega : 2 * (k + 1) ≤ N + 2), if_neg h5,
          if_pos h3, h6, h7]
        have hNk : ((N + 2 : ℕ) : ℚ) = 2 * ((k : ℚ) + 1) := by
          rw [h4]; push_cast; ring
        rw [hNk]
        simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      · have h5 : ¬ (2 * (k + 1) ≤ N + 1) := by omega
        have h6 : ¬ (2 * (k + 1) ≤ N + 2) := by omega
        have h7 : ¬ (2 * k ≤ N) := by omega
        rw [bchCoef, bchCoef, bchCoef, if_neg h5, if_neg h6, if_neg h7]
        ring

