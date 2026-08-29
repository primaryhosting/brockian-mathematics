import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a primitive root modulo the prime `p` if its residue generates the
multiplicative group `(ZMod p)ˣ`, i.e. it has multiplicative order `p - 1`. -/

theorem isPrimitiveRootMod_two_five : IsPrimitiveRootMod 2 5 := by
  show orderOf ((2 : ℤ) : ZMod 5) = 5 - 1
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hqd
  have hq4 : q ≤ 4 := Nat.le_of_dvd (by norm_num) hqd
  have := hq.two_le
  interval_cases q <;> revert hqd <;> decide

/-- `2` is a primitive root modulo `11`. -/
