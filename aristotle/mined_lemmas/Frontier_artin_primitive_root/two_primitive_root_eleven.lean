import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root modulo `p`* when its residue generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/

lemma two_primitive_root_eleven : IsPrimitiveRootMod 2 11 := by
  have : ((2 : ℤ) : ZMod 11) = (2 : ZMod 11) := by norm_num
  rw [IsPrimitiveRootMod, this]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hdvd
  have h1 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 := hq.two_le
  interval_cases q
  all_goals (revert hdvd hq; decide)

