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

lemma artinPrimes_neg_one_subset : artinPrimes (-1) ⊆ {2, 3} := by
  rintro p ⟨hp, hprim⟩
  have hcast : (((-1 : ℤ) : ZMod p)) = -1 := by push_cast; ring
  have h2 : ((-1 : ZMod p)) ^ 2 = 1 := by ring
  have hdvd : orderOf ((-1 : ZMod p)) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [IsPrimitiveRootMod, hcast] at hprim
  rw [hprim] at hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have := hp.two_le
  have : p = 2 ∨ p = 3 := by omega
  simpa using this

