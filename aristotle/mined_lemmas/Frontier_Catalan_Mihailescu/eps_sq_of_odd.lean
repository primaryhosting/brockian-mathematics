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

lemma eps_sq_of_odd {m : ℕ} (h : Odd m) : eps m ^ 2 = 1 := by
  obtain ⟨n, rfl⟩ := h
  have hpow : (gi ^ (2 * n + 1)) = ((-1 : GaussianInt)) ^ n * gi := by
    rw [pow_add, pow_mul, gi_sq, pow_one]
  rw [eps, hpow]
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow]; norm_num [gi]
  · rw [h.neg_one_pow]; simp [gi]

