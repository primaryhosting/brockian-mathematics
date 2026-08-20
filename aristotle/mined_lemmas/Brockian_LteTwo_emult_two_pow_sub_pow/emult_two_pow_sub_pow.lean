import Mathlib
namespace Brockian.LteTwo

/-- Auxiliary: the integer form of lifting-the-exponent at `p = 2`, phrased with
`emultiplicity`.  This is exactly `Int.two_pow_sub_pow'` from Mathlib. -/

theorem emult_two_pow_sub_pow {x y : ℤ} (n : ℕ) (hxy : 4 ∣ x - y) (hx : ¬ (2 : ℤ) ∣ x) :
    emultiplicity 2 (x ^ n - y ^ n) = emultiplicity 2 (x - y) + emultiplicity (2 : ℤ) n :=
  Int.two_pow_sub_pow' n hxy hx

/-- Auxiliary: `Nat.factorization` at a prime equals `padicValNat`. -/
