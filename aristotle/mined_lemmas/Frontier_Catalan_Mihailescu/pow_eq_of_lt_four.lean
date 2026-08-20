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

lemma pow_eq_of_lt_four {z n v : ℕ} (hz : 1 < z) (hn : 1 ≤ n) (hv : v < 4) (h : z ^ n = v) :
    n = 1 ∧ z = v := by
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hn1 : n = 1 := by omega
    subst hn1
    exact ⟨rfl, by simpa using h⟩
  · exfalso
    have h1 : 2 ^ n ≤ z ^ n := Nat.pow_le_pow_left hz n
    have h3 : (2:ℕ) ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    norm_num at h3
    omega

/-- **Reduction to prime exponents.**  If Catalan's equation has no nontrivial solutions with
both exponents prime (other than `3 ^ 2 - 2 ^ 3 = 1`), then it has none at all: the full
statement `CatalanMihailescuStatement` follows. -/
