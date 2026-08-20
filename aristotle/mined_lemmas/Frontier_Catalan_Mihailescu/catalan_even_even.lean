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

lemma catalan_even_even {x y p q : ℕ} (hy : 1 ≤ y) (hp : Even p) (hq : Even q) :
    x ^ p ≠ y ^ q + 1 := by
  intro h
  obtain ⟨m, rfl⟩ := hp
  obtain ⟨k, rfl⟩ := hq
  have h1 : (x ^ m) ^ 2 = (y ^ k) ^ 2 + 1 := by
    rw [← pow_mul, ← pow_mul]; ring_nf; ring_nf at h; omega
  exact catalan_equal_exponents (Nat.one_le_iff_ne_zero.2 (by positivity)) le_rfl h1

/-- `x ^ 2 = y ^ q + 1` has no solutions with `y` odd, `y > 1` and `q ≥ 2`. -/
