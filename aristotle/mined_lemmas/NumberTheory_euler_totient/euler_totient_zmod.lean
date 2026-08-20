/-
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-- Euler's theorem, `ZMod` form: any unit `a` of `ZMod n` satisfies
`a ^ Nat.totient n = 1`. -/

theorem euler_totient_zmod {n : ℕ} (a : ZMod n) (ha : IsUnit a) :
    a ^ Nat.totient n = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have : u ^ Nat.totient n = 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- `ZMod 0 = ℤ`, totient 0 = 0
      simp
    · haveI : NeZero n := ⟨hn.ne'⟩
      rw [← ZMod.card_units_eq_totient n]
      exact pow_card_eq_one
  rw [← Units.val_pow_eq_pow_val, this, Units.val_one]

/-- Euler's theorem, integer/`Nat` form: if `a` and `n` are coprime then
`a ^ Nat.totient n ≡ 1 [MOD n]`. -/
