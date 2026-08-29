import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib bridge

The target theorem `Brockian.GoldbachWheelK2_727` lives in a Mathlib-free file (a module
docstring may not precede `import`, so the required header comment forces that file to be
import-free).  Here we identify the primality predicate used there with Mathlib's
`Nat.Prime` and restate the result accordingly.
-/

namespace Brockian

/-- The from-first-principles primality predicate agrees with Mathlib's `Nat.Prime`. -/

theorem noFactorFrom_sound :
    ∀ (f d n k : Nat), noFactorFrom f d n = true → d ≤ k → k * k ≤ n → ¬ (k ∣ n) := by
  intro f
  induction f with
  | zero => intro d n k h _ _ _; exact Bool.noConfusion h
  | succ f ih =>
      intro d n k h hdk hkk hdvd
      rw [noFactorFrom] at h
      by_cases hlt : n < d * d
      · exact absurd (Nat.le_trans (Nat.mul_le_mul hdk hdk) hkk) (Nat.not_le.mpr hlt)
      · rw [if_neg hlt] at h
        by_cases hmod : n % d == 0
        · rw [if_pos hmod] at h; exact Bool.noConfusion h
        · rw [if_neg hmod] at h
          rcases Nat.eq_or_lt_of_le hdk with rfl | hlt'
          · obtain ⟨c, rfl⟩ := hdvd
            exact hmod (by simp [Nat.mul_mod_right])
          · exact ih (d + 1) n k h hlt' hkk hdvd

/-- The fast primality test is sound. -/
