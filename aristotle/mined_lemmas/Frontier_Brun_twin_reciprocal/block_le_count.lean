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

lemma block_le_count (i : ℕ) :
    block i ≤ (1/(2:ℝ)^i) * #((range (2^(i+1))).filter (fun n => n.Prime ∧ (n+2).Prime)) := by
  classical
  have h1 : ∀ n ∈ Ico (2^i) (2^(i+1)),
      twinRecip n ≤ (if n.Prime ∧ (n+2).Prime then (1:ℝ)/2^i else 0) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    unfold twinRecip
    split
    · apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast hn.1
    · exact le_rfl
  calc block i
      ≤ ∑ n ∈ Ico (2^i) (2^(i+1)), (if n.Prime ∧ (n+2).Prime then (1:ℝ)/2^i else 0) :=
        Finset.sum_le_sum h1
    _ = (1/(2:ℝ)^i) * #((Ico (2^i) (2^(i+1))).filter (fun n => n.Prime ∧ (n+2).Prime)) := by
        rw [← Finset.sum_filter, Finset.sum_const]
        simp [nsmul_eq_mul, mul_comm]
    _ ≤ (1/(2:ℝ)^i) * #((range (2^(i+1))).filter (fun n => n.Prime ∧ (n+2).Prime)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hsub : (Ico (2^i) (2^(i+1))).filter (fun n => n.Prime ∧ (n+2).Prime) ⊆
            (range (2^(i+1))).filter (fun n => n.Prime ∧ (n+2).Prime) := by
          apply Finset.filter_subset_filter
          intro x hx
          exact Finset.mem_range.2 (Finset.mem_Ico.1 hx).2
        exact_mod_cast Finset.card_le_card hsub

/-- The geometric ratio used in the error estimate. -/
