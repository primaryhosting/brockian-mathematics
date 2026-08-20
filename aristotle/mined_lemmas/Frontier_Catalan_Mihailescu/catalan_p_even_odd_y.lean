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

lemma catalan_p_even_odd_y {x y p q : ℕ} (hy : 1 < y) (hq : 2 ≤ q) (hp : Even p)
    (hodd : Odd y) : x ^ p ≠ y ^ q + 1 := by
  intro h
  obtain ⟨m, rfl⟩ := hp
  refine catalan_sq_odd hy hq hodd (x := x ^ m) ?_
  rw [← pow_mul, show m * 2 = m + m by ring]
  exact h

/-- Catalan's equation when the smaller power is a power of two:
`x ^ p = 2 ^ q + 1` forces `9 = 8 + 1`. -/
