import Mathlib
namespace Brockian.LteTwo

/-- Auxiliary: the integer form of lifting-the-exponent at `p = 2`, phrased with
`emultiplicity`.  This is exactly `Int.two_pow_sub_pow'` from Mathlib. -/

theorem factorization_two (m : ℕ) : m.factorization 2 = padicValNat 2 m := by
  exact Nat.factorization_def m Nat.prime_two

/-- Auxiliary: the natural-number version, phrased with `padicValNat`. -/
