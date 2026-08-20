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

lemma sum_block_le (I : ℕ) :
    ∑ i ∈ range I, block i ≤ (aa 16 : ℝ) + (∑' j, vv j) + 2 * (1 - rt)⁻¹ := by
  classical
  have hpt : ∀ i, block i ≤ (if i < aa 16 then (1:ℝ) else 0)
      + (if aa 16 ≤ i then 4 * Real.exp (-(jj i : ℝ)) else 0) + 2 * rt^i := by
    intro i
    by_cases h : i < aa 16
    · rw [if_pos h, if_neg (by omega)]
      have := block_le_one i
      have h2 : (0:ℝ) ≤ 2 * rt^i :=
        mul_nonneg (by norm_num) (pow_nonneg rt_nonneg i)
      linarith
    · rw [if_neg h, if_pos (by omega)]
      have hi : aa 16 ≤ i := by omega
      obtain ⟨h1, h2⟩ := jj_spec hi
      have := block_le i (jj i) h1 h2
      linarith
  have hgeo : ∑ i ∈ range I, (2 : ℝ) * rt^i ≤ 2 * (1 - rt)⁻¹ := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hsum : Summable (fun i : ℕ => rt^i) := summable_geometric_of_lt_one rt_nonneg rt_lt_one
    calc ∑ i ∈ range I, rt^i ≤ ∑' i : ℕ, rt^i :=
          Summable.sum_le_tsum _ (fun i _ => pow_nonneg rt_nonneg i) hsum
      _ = (1 - rt)⁻¹ := tsum_geometric_of_lt_one rt_nonneg rt_lt_one
  have hcount : ∑ i ∈ range I, (if i < aa 16 then (1:ℝ) else 0) ≤ (aa 16 : ℝ) := by
    calc ∑ i ∈ range I, (if i < aa 16 then (1:ℝ) else 0)
        = (#((range I).filter (fun i => i < aa 16)) : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const]
          simp
      _ ≤ (aa 16 : ℝ) := by
          have hsub : (range I).filter (fun i => i < aa 16) ⊆ range (aa 16) := by
            intro x hx
            exact Finset.mem_range.2 (Finset.mem_filter.1 hx).2
          have := Finset.card_le_card hsub
          rw [Finset.card_range] at this
          exact_mod_cast this
  calc ∑ i ∈ range I, block i
      ≤ ∑ i ∈ range I, ((if i < aa 16 then (1:ℝ) else 0)
          + (if aa 16 ≤ i then 4 * Real.exp (-(jj i : ℝ)) else 0) + 2 * rt^i) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = (∑ i ∈ range I, (if i < aa 16 then (1:ℝ) else 0))
        + (∑ i ∈ range I, (if aa 16 ≤ i then 4 * Real.exp (-(jj i : ℝ)) else 0))
        + ∑ i ∈ range I, (2:ℝ) * rt^i := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ (aa 16 : ℝ) + (∑' j, vv j) + 2 * (1 - rt)⁻¹ := by
        have := tail_sum_le I
        linarith

/-- Dyadic decomposition of a partial sum. -/
