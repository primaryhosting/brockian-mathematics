/-
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-- **Euler's theorem** (unit form): for `a : ZMod n` a unit, `a ^ φ n = 1`. -/

theorem euler_totient_zmod {n : ℕ} [NeZero n] {a : ZMod n} (ha : IsUnit a) :
    a ^ Nat.totient n = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have hcard : Fintype.card (ZMod n)ˣ = Nat.totient n := ZMod.card_units_eq_totient n
  have := pow_card_eq_one (G := (ZMod n)ˣ) (x := u)
  rw [hcard] at this
  rw [← Units.val_pow_eq_pow_val, this, Units.val_one]

/-- **Euler's theorem** (congruence form): if `a` and `n` are coprime, then
`a ^ φ n ≡ 1 [MOD n]`. -/
