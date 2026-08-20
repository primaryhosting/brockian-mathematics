import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command,
-- including module documentation, so the header block above sits just after
-- the single `import Mathlib` line.

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian

/-! ### A kernel-friendly primality test

`Nat.decidablePrime` performs `Θ(n)` trial divisions and is far too slow for
kernel reduction on a few hundred numbers, so we use a small trial-division
test up to `√n` (with fuel) together with a soundness proof. -/

/-- `trialAux n f d` checks that no `e` with `d ≤ e` and `e * e ≤ n` divides `n`,
using `f` units of fuel; it returns `false` when the fuel runs out. -/

theorem trialAux_sound (n : ℕ) :
    ∀ f d, trialAux n f d = true → ∀ e, d ≤ e → e * e ≤ n → ¬ e ∣ n := by
  intro f
  induction f with
  | zero => intro d h; simp [trialAux] at h
  | succ f ih =>
    intro d h e hde hee hdvd
    rw [trialAux] at h
    by_cases h1 : n < d * d
    · exact absurd hee (by nlinarith [Nat.mul_le_mul hde hde])
    · simp only [h1, if_false] at h
      by_cases h2 : n % d == 0
      · simp [h2] at h
      · simp only [h2] at h
        rcases eq_or_lt_of_le hde with rfl | hlt
        · simp only [beq_iff_eq] at h2
          exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
        · exact ih (d + 1) h e hlt hee hdvd

