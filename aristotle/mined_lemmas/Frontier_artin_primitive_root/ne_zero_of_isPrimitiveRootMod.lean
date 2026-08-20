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

lemma ne_zero_of_isPrimitiveRootMod {a : ℤ} {p : ℕ} (hp : p.Prime)
    (h : IsPrimitiveRootMod a p) : (a : ZMod p) ≠ 0 := by
  have hpow : ((a : ZMod p)) ^ (p - 1) = 1 := by
    have := pow_orderOf_eq_one ((a : ZMod p))
    rwa [h] at this
  intro h0
  have h2 := hp.two_le
  rw [h0, zero_pow (by omega : p - 1 ≠ 0)] at hpow
  haveI : Fact p.Prime := ⟨hp⟩
  exact zero_ne_one hpow

/-- A perfect square is a primitive root only modulo `2`. -/
