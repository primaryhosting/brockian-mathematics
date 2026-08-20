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

lemma catalan_equal_exponents {x y n : ℕ} (hy : 1 ≤ y) (hn : 2 ≤ n) :
    x ^ n ≠ y ^ n + 1 := by
  intro h
  have hxy : y < x := by
    by_contra hc
    push_neg at hc
    have := Nat.pow_le_pow_left hc n
    omega
  have h1 : (y + 1) ^ n ≤ x ^ n := Nat.pow_le_pow_left hxy n
  have h2 := succ_pow_ge y n hy hn
  omega

/-- Two perfect powers with *both* exponents even are never consecutive. -/
