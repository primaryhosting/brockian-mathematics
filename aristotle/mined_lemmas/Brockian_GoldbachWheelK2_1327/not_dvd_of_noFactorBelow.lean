/-
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace Brockian

/-- `noFactorBelow n k` is `true` exactly when no `d` with `2 ≤ d ≤ k` divides `n`. -/

theorem not_dvd_of_noFactorBelow :
    ∀ (k n d : ℕ), noFactorBelow n k = true → 2 ≤ d → d ≤ k → ¬ d ∣ n := by
  intro k
  induction k with
  | zero => intro n d _ hd hle; omega
  | succ k ih =>
    match k with
    | 0 => intro n d _ hd hle; omega
    | (k + 1) =>
      intro n d h hd hle
      rw [noFactorBelow, Bool.and_eq_true, bne_iff_ne] at h
      obtain ⟨h1, h2⟩ := h
      rcases eq_or_lt_of_le hle with rfl | hlt
      · intro hdvd
        exact h1 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact ih n d h2 hd (by omega)

