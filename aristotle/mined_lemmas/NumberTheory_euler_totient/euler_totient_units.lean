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

theorem euler_totient_units {n : ℕ} (u : (ZMod n)ˣ) : u ^ Nat.totient n = 1 :=
  ZMod.pow_totient u

/-- **Euler's theorem**, congruence form: if `a` and `n` are coprime natural numbers then
`a ^ φ n ≡ 1 [MOD n]`.  This is Mathlib's `Nat.ModEq.pow_totient`. -/
