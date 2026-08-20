/-
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000000

namespace Brockian

/-- `trialDivB n f d` performs trial division of `n` by the successive divisors
`d, d+1, ...` (using at most `f` steps), stopping successfully as soon as the
divisor exceeds `√n`. It returns `true` only when no divisor `≥ d` with
`k * k ≤ n` divides `n`. -/

theorem trialDivB_sound :
    ∀ (f n d : ℕ), trialDivB n f d = true → ∀ k, d ≤ k → k * k ≤ n → ¬ k ∣ n := by
  intro f
  induction f with
  | zero => intro n d h; simp [trialDivB] at h
  | succ f ih =>
      intro n d h k hdk hk hdvd
      rw [trialDivB] at h
      by_cases hmod : n % d == 0
      · simp [hmod] at h
      · simp only [hmod] at h
        have hnd : ¬ d ∣ n := by
          intro hd
          exact hmod (by simpa using Nat.mod_eq_zero_of_dvd hd)
        by_cases hlt : n < (d + 1) * (d + 1)
        · -- only `k = d` is possible
          rcases Nat.lt_or_ge k (d + 1) with hk1 | hk1
          · have : k = d := by omega
            exact hnd (this ▸ hdvd)
          · have : (d + 1) * (d + 1) ≤ k * k := Nat.mul_le_mul hk1 hk1
            omega
        · simp only [hlt, if_false] at h
          rcases Nat.lt_or_ge k (d + 1) with hk1 | hk1
          · have : k = d := by omega
            exact hnd (this ▸ hdvd)
          · exact ih n (d + 1) h k hk1 hk hdvd

/-- The Boolean primality test is sound. -/
