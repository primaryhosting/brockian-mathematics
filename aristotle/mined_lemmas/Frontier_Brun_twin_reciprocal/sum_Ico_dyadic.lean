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

lemma sum_Ico_dyadic (I : ℕ) :
    ∑ n ∈ Ico 1 (2^I), twinRecip n = ∑ i ∈ range I, block i := by
  induction I with
  | zero => simp
  | succ I ih =>
    rw [Finset.sum_range_succ, ← ih, block]
    rw [Finset.sum_Ico_consecutive]
    · exact Nat.one_le_two_pow
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges. -/
