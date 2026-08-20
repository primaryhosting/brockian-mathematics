import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Brockian

/-- Trial division helper: `noFactorFrom f d n` is `true` when none of
`d, d+1, …` (up to `f` steps, stopping as soon as the divisor squared exceeds `n`)
divides `n`. -/

theorem noFactorFrom_spec : ∀ (f d n : ℕ), noFactorFrom f d n = true →
    ∀ k, d ≤ k → k < d + f → k * k ≤ n → ¬ k ∣ n := by
  intro f
  induction f with
  | zero => intro d n _ k hdk hlt _; omega
  | succ f ih =>
    intro d n h k hdk hlt hkk hdvd
    rw [noFactorFrom] at h
    by_cases h1 : n < d * d
    · have : d * d ≤ k * k := Nat.mul_le_mul hdk hdk
      omega
    · rw [if_neg h1] at h
      by_cases h2 : n % d == 0
      · rw [if_pos h2] at h; exact absurd h (by simp)
      · rw [if_neg h2] at h
        rcases eq_or_lt_of_le hdk with rfl | hlt2
        · simp only [beq_iff_eq] at h2
          exact h2 (Nat.dvd_iff_mod_eq_zero.mp hdvd)
        · exact ih (d + 1) n h k hlt2 (by omega) hkk hdvd

/-- Soundness of the Boolean primality test. -/
