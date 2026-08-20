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

lemma lt_two_pow_sub {r : ℕ} (h : 5 ≤ r) : r < 2 ^ (r - 2) := by
  induction r, h using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
      have h1 : 2 ^ (r + 1 - 2) = 2 * 2 ^ (r - 2) := by
        rw [show r + 1 - 2 = (r - 2) + 1 by omega, pow_succ]; ring
      omega

/-! ### Special cases of Catalan's equation -/

/-- Two perfect powers with the *same* exponent are never consecutive. -/
