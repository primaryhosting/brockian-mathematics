/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This module is deliberately import-free (Lean forbids `import` after the header
-- comment above), so primality is spelled out from first principles here.  The
-- companion module `RequestProject.GoldbachWheelK2_1327Mathlib` proves that
-- `Brockian.IsPrimeNat` coincides with Mathlib's `Nat.Prime`, and restates the
-- main theorem in Mathlib's vocabulary.

namespace Brockian

set_option maxRecDepth 100000

/-- Primality, from first principles: `n` is at least `2` and its only divisors are
`1` and `n`. -/

theorem trialAux_spec :
    ∀ fuel n d, trialAux fuel n d = true →
      ∀ e, d ≤ e → e * e ≤ n → e < d + fuel → ¬ e ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro n d _ e hde _ hlt; omega
  | succ fuel ih =>
      intro n d h e hde hen hlt
      rw [trialAux] at h
      split at h
      · rename_i hdd
        exact absurd hen (by
          have : d * d ≤ e * e := Nat.mul_le_mul hde hde
          omega)
      · split at h
        · exact absurd h (by simp)
        · rename_i hmod
          rcases Nat.eq_or_lt_of_le hde with rfl | hlt'
          · rintro ⟨c, rfl⟩
            exact hmod (Nat.mul_mod_right _ c)
          · exact ih n (d + 1) h e (by omega) hen (by omega)

