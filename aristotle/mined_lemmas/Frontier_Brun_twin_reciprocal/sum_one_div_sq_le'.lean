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

lemma sum_one_div_sq_le' (n : ℕ) (hn : 1 ≤ n) :
    ∑ b ∈ Icc 1 n, (1 : ℝ) / (b : ℝ) ^ 2 ≤ 2 - 1 / n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hn with h | h
    · simp [← h]; norm_num
    · have hm : 1 ≤ m := by omega
      rw [Finset.sum_Icc_succ_top (by omega)]
      have := ih hm
      have hm0 : (0:ℝ) < m := by exact_mod_cast hm
      have h1 : (1:ℝ)/((m:ℝ)+1)^2 ≤ 1/m - 1/(m+1) := by
        have he : 1/(m:ℝ) - 1/((m:ℝ)+1) = 1/((m:ℝ)*((m:ℝ)+1)) := by field_simp; ring
        rw [he]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      push_cast
      linarith

/-- The sum of `1/b²` for `b ≤ n` is at most `2`. -/
