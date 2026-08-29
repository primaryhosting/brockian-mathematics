import Mathlib
/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

/-- A *Catalan solution*: a pair of consecutive perfect powers, i.e. natural numbers with
`x ^ p = y ^ q + 1`, all of `x, y, p, q` being at least `2`. -/

lemma pow_odd_modEq_self {u m e : ℕ} (he : Odd e) (h : u ^ 2 ≡ 1 [MOD m]) :
    u ^ e ≡ u [MOD m] := by
  obtain ⟨t, rfl⟩ := he
  have hrw : u ^ (2 * t + 1) = (u ^ 2) ^ t * u := by ring
  rw [hrw]
  calc (u ^ 2) ^ t * u ≡ 1 ^ t * u [MOD m] := Nat.ModEq.mul (Nat.ModEq.pow t h) (Nat.ModEq.refl u)
    _ = u := by ring

/-- `u ^ m + 1` is never a power of two when `u ≥ 3` and `m ≥ 3` is odd. -/
