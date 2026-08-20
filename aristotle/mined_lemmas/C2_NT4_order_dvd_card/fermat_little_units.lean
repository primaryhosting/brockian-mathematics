import Mathlib
namespace C2.NT4

/-- The order of a unit in `ZMod p` divides `p - 1`, the cardinality of `(ZMod p)ˣ`. -/

theorem fermat_little_units (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by
  rw [← ZMod.card_units p]
  exact pow_card_eq_one

end C2.NT4

