import Mathlib
/-!
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- **Euler's theorem** (Fermat–Euler totient theorem): if `a : ZMod n` is a unit, then
`a ^ Nat.totient n = 1`.  This is the `ZMod`-element form of Mathlib's `ZMod.pow_totient`
(which is stated for `x : (ZMod n)ˣ`). -/

theorem euler_totient {n : ℕ} {a : ZMod n} (ha : IsUnit a) : a ^ Nat.totient n = 1 := by
  obtain ⟨u, rfl⟩ := ha
  rw [← Units.val_pow_eq_pow_val, ZMod.pow_totient u, Units.val_one]

/-- **Euler's theorem**, units form: every unit of `ZMod n` has order dividing `φ n`.
This is exactly Mathlib's `ZMod.pow_totient`. -/
