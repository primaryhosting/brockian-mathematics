/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `IsPrimitiveRootMod a p` says that the integer `a` is a primitive root modulo `p`, i.e.
the residue of `a` generates the multiplicative group `(ZMod p)ˣ`, which for a prime `p`
amounts to the multiplicative order of `a` in `ZMod p` being exactly `p - 1`. -/

lemma isPrimitiveRootMod_two_three : IsPrimitiveRootMod 2 3 := by
  have h : ((2 : ℤ) : ZMod 3) = (2 : ZMod 3) := cast_two 3
  show orderOf ((2 : ℤ) : ZMod 3) = 3 - 1
  rw [h]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hdvd
  have hq2 : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hq1 : 2 ≤ q := hq.two_le
  interval_cases q <;> revert hdvd <;> decide

