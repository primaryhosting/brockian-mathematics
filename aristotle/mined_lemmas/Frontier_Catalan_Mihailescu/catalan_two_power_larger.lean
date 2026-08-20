import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The full Catalan–Mihăilescu theorem, as a statement (it is *not* proved in this file):
the only pair of consecutive perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`. -/

lemma catalan_two_power_larger {y p q k : ℕ} (hy : 1 < y) (hp : 1 < p) (hq : 1 < q) (hk : 1 ≤ k) :
    (2 ^ k) ^ p ≠ y ^ q + 1 := by
  rw [← pow_mul]
  exact catalan_two_pow_sub_one hy (by nlinarith) hq

/-- A reduction: any solution with `q` even has `x` odd, `y` even and `p` odd. -/
