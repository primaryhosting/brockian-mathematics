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

lemma summable_vv : Summable vv := by
  have hlt : (2/Real.exp 1 : ℝ) < 1 := by
    rw [div_lt_one (Real.exp_pos 1)]
    have := Real.exp_one_gt_d9
    linarith
  have h : ‖(2/Real.exp 1 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hlt
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 h
  have h2 := summable_geometric_of_lt_one (r := (2/Real.exp 1 : ℝ)) (by positivity) hlt
  have h3 : Summable (fun j : ℕ => ((j:ℝ)+1) * (2/Real.exp 1)^j) := by
    simpa [add_mul] using h1.add h2
  have h4 := h3.mul_left 928
  have heq : vv = fun j : ℕ => 928 * (((j:ℝ)+1) * (2/Real.exp 1)^j) := by
    funext j; unfold vv; ring
  rw [heq]
  exact h4

