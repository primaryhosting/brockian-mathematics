import Mathlib
namespace C2.NT4

/-- The order of a unit in `ZMod p` divides `p - 1`, the cardinality of `(ZMod p)ˣ`. -/

theorem order_dvd_card (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : orderOf a ∣ (p - 1) := by
  rw [← ZMod.card_units p]
  exact orderOf_dvd_card

/-- The multiplicative group of `ZMod p` is cyclic, so it has a generator of order `p - 1`. -/
