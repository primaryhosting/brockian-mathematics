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

lemma prod_one_sub_le_exp (hQ : ∀ p ∈ Q, 3 ≤ p) :
    ∏ p ∈ Q, (1 - 2/(p:ℝ)) ≤ Real.exp (-(∑ p ∈ Q, 2/(p:ℝ))) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have h3 : (3:ℝ) ≤ p := by exact_mod_cast hQ p hp
    have : 2/(p:ℝ) ≤ 2/3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
    linarith
  · intro p _
    have := Real.add_one_le_exp (-(2/(p:ℝ)))
    linarith

/-- Full inclusion–exclusion sum over all subsets. -/
