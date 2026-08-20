import Mathlib
import RequestProject.Brun.Final

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the required header comment appears immediately after the imports.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The summand is `1/n` whenever `n` and `n + 2` are both prime, and `0` otherwise; the value of
its sum is Brun's constant.  Convergence is proved from scratch by a Brun pure sieve; see the
development in `RequestProject/Brun/`. -/

lemma sum_one_div_sq_le (n : ℕ) : ∑ b ∈ Icc 1 n, (1 : ℝ) / (b : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have := sum_one_div_sq_le' n h
    have : (0:ℝ) < n := by exact_mod_cast h
    have h2 := sum_one_div_sq_le' n (by omega)
    have : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
    linarith

/-- Bounding the harmonic sum by (squarefree sum) * (sum of inverse squares). -/
