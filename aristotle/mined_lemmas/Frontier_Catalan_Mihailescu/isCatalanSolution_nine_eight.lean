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

theorem isCatalanSolution_nine_eight : IsCatalanSolution 3 2 2 3 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The full statement of the Catalan–Mihăilescu theorem: `3 ^ 2 - 2 ^ 3 = 1` is the only
solution of `x ^ p - y ^ q = 1` in natural numbers `x, y, p, q ≥ 2`. -/
