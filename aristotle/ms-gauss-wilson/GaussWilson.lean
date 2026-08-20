import Mathlib
namespace Brockian.GaussWilson
/-- Gauss's generalization of Wilson's theorem: the product of the units of ℤ/nℤ equals −1
    when n has a primitive root (n = 1,2,4,p^k,2p^k) and +1 otherwise. Here the clean universal
    fact: the product of all units of ℤ/nℤ is its own inverse, i.e. squares to 1. -/
theorem prod_units_sq_eq_one (n : ℕ) [NeZero n] :
    (∏ u : (ZMod n)ˣ, u) ^ 2 = 1 := by
  sorry
end Brockian.GaussWilson
