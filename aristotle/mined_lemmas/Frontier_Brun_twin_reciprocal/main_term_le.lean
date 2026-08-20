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

lemma main_term_le (hQ : ∀ p ∈ Q, 3 ≤ p) (K : ℕ) :
    ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ))
      ≤ Real.exp (-(∑ p ∈ Q, 2/(p:ℝ)))
        + Real.exp (Real.exp 1 * (∑ p ∈ Q, 2/(p:ℝ)) - (K+1)) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not Q.powerset (fun T => T.card ≤ K)
    (fun T => (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ)))
  rw [sum_powerset_alt Q] at hsplit
  have hpos : ∀ p ∈ Q, (0:ℝ) < p := by
    intro p hp
    have : (3:ℝ) ≤ p := by exact_mod_cast hQ p hp
    linarith
  have habs : -∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K), (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ))
      ≤ ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K), ∏ p ∈ T, (2/(p:ℝ)) := by
    calc -∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K),
            (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ))
        ≤ |∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K),
            (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ))| := neg_le_abs _
      _ ≤ ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K),
            |(-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K), ∏ p ∈ T, (2/(p:ℝ)) := by
          refine Finset.sum_congr rfl fun T hT => ?_
          have hTQ : T ⊆ Q := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg]
          exact Finset.prod_nonneg fun p hp => by
            have := hpos p (hTQ hp); positivity
  have h1 := prod_one_sub_le_exp Q hQ
  have h2 := tail_le Q hQ K
  linarith

/-- Sum over small subsets, by cardinality (real-valued version). -/
