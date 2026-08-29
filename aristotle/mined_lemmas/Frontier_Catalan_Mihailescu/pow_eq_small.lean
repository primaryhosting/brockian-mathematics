import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The full Catalan–Mihăilescu statement: `8` and `9` are the only consecutive
perfect powers, i.e. the only solution of `x ^ p = y ^ q + 1` in integers
`x, y, p, q > 1` is `3 ^ 2 = 2 ^ 3 + 1`. -/

private lemma pow_eq_small {x n c : ℕ} (hx : 1 < x) (hc : 2 ≤ c) (hc4 : c ≤ 3)
    (h : x ^ n = c) : n = 1 ∧ x = c := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at h; omega
  have hn : n = 1 := by
    by_contra hne
    have h2 : 2 ≤ n := by omega
    have : 2 ^ 2 ≤ x ^ n :=
      le_trans (Nat.pow_le_pow_left hx 2) (Nat.pow_le_pow_right (by omega) h2)
    omega
  subst hn; simpa using h

/-- Reduction of the Catalan–Mihăilescu statement to the case of prime exponents. -/
