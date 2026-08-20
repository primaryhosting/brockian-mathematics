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

lemma sum_powerset_alt (Q : Finset ℕ) :
    ∑ T ∈ Q.powerset, (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ)) = ∏ p ∈ Q, (1 - 2/(p:ℝ)) := by
  have h := Finset.prod_add (fun p : ℕ => -(2/(p:ℝ))) (fun _ => (1:ℝ)) Q
  simp only [Finset.prod_const_one, mul_one] at h
  rw [show (fun p : ℕ => -(2/(p:ℝ)) + 1) = (fun p : ℕ => 1 - 2/(p:ℝ)) by funext p; ring] at h
  rw [h]
  exact Finset.sum_congr rfl fun T _ => (Finset.prod_neg (fun p : ℕ => (2/(p:ℝ)))).symm

/-- The tail of the inclusion–exclusion sum is small. -/
