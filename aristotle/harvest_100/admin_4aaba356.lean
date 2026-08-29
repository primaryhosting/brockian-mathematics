import Mathlib

/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter

namespace Brockian

/-- The truncated singular series: the partial sum `∑_{q = 1}^{Q} a q` of the local
densities `a q`. -/
noncomputable def singularPartial (a : ℕ → ℝ) (Q : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 Q, a q

lemma singularPartial_eq_range (a : ℕ → ℝ) (Q : ℕ) :
    singularPartial a Q = ∑ i ∈ Finset.range Q, a (i + 1) := by
  induction Q with
  | zero => simp [singularPartial]
  | succ Q ih =>
      rw [singularPartial, Finset.sum_Icc_succ_top (by omega), ← singularPartial, ih,
        Finset.sum_range_succ]

/-- Telescoping bound: the tail `∑_{i < N} 1/(i+Q+1)^2` is at most `1/Q - 1/(Q+N)`. -/
lemma sum_inv_sq_shift_le (Q : ℕ) (hQ : 1 ≤ Q) (N : ℕ) :
    ∑ i ∈ Finset.range N, (1:ℝ) / ((i : ℝ) + Q + 1) ^ 2 ≤ 1 / (Q : ℝ) - 1 / ((Q : ℝ) + N) := by
  have hQ0 : (0:ℝ) < Q := by exact_mod_cast hQ
  induction N with
  | zero => simp
  | succ N ih =>
      have hN0 : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have h1 : (0:ℝ) < (Q : ℝ) + N := by linarith
      have h2 : (0:ℝ) < (Q : ℝ) + N + 1 := by linarith
      have key : (1:ℝ) / ((N : ℝ) + Q + 1) ^ 2
          ≤ 1 / ((Q : ℝ) + N) - 1 / ((Q : ℝ) + N + 1) := by
        rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg ((N : ℝ) + Q)]
      rw [Finset.sum_range_succ]
      push_cast
      calc ∑ i ∈ Finset.range N, (1:ℝ) / ((i : ℝ) + Q + 1) ^ 2 + 1 / ((N : ℝ) + Q + 1) ^ 2
          ≤ (1 / (Q : ℝ) - 1 / ((Q : ℝ) + N)) + (1 / ((Q : ℝ) + N) - 1 / ((Q : ℝ) + N + 1)) := by
            exact add_le_add ih key
        _ = 1 / (Q : ℝ) - 1 / ((Q : ℝ) + (N + 1)) := by ring_nf
      
/-- **Effective convergence rate for a singular series.**

If the local densities `a q` obey the square-root-cancellation style bound
`|a q| ≤ C / q ^ 2` for all `q ≥ 1`, then the singular series converges, and its
truncation at `Q` differs from the full series by at most `C / Q`. -/
theorem SingularSeriesConvergenceRate {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ q : ℕ, 1 ≤ q → |a q| ≤ C / (q : ℝ) ^ 2) :
    ∃ S : ℝ, Tendsto (fun Q => singularPartial a Q) atTop (nhds S) ∧
      ∀ Q : ℕ, 1 ≤ Q → |S - singularPartial a Q| ≤ C / (Q : ℝ) := by
  -- `C` is nonnegative
  have hC : 0 ≤ C := by
    have := ha 1 le_rfl
    simpa using le_trans (abs_nonneg _) this
  set b : ℕ → ℝ := fun i => a (i + 1) with hb
  have hbbd : ∀ i : ℕ, |b i| ≤ C / ((i : ℝ) + 1) ^ 2 := by
    intro i
    have := ha (i + 1) (by omega)
    simpa [hb] using this
  -- comparison series is summable
  have hsum_g : Summable (fun i : ℕ => C / ((i : ℝ) + 1) ^ 2) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow).2 (by norm_num)
    have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 h
      simpa [Nat.cast_add, Nat.cast_one] using this
    simpa [mul_one_div] using h1.mul_left C
  have hsumb : Summable b := by
    refine Summable.of_norm_bounded hsum_g ?_
    intro i
    simpa [Real.norm_eq_abs] using hbbd i
  refine ⟨∑' i, b i, ?_, ?_⟩
  · have := hsumb.hasSum.tendsto_sum_nat
    simpa [singularPartial_eq_range a, hb] using this
  · intro Q hQ
    have hQ0 : (0:ℝ) < Q := by exact_mod_cast hQ
    -- the difference is the tail of the series
    have htail : (∑' i, b i) - ∑ i ∈ Finset.range Q, b i = ∑' i, b (i + Q) := by
      have := hsumb.sum_add_tsum_nat_add Q
      linarith [this]
    have hsummable_abs : Summable (fun i => |b (i + Q)|) := by
      have : Summable (fun i => |b i|) := hsumb.abs
      exact (summable_nat_add_iff Q).2 this
    have habs : |∑' i, b (i + Q)| ≤ ∑' i, |b (i + Q)| := by
      simpa [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (f := fun i => b (i + Q)) (by simpa [Real.norm_eq_abs] using hsummable_abs)
    have hbound : ∑' i, |b (i + Q)| ≤ C / (Q : ℝ) := by
      refine Real.tsum_le_of_sum_range_le (fun i => abs_nonneg _) ?_
      intro N
      have step : ∀ i : ℕ, |b (i + Q)| ≤ C * (1 / ((i : ℝ) + Q + 1) ^ 2) := by
        intro i
        have := hbbd (i + Q)
        have hcast : ((i + Q : ℕ) : ℝ) + 1 = (i : ℝ) + Q + 1 := by push_cast; ring
        calc |b (i + Q)| ≤ C / (((i + Q : ℕ) : ℝ) + 1) ^ 2 := this
          _ = C * (1 / ((i : ℝ) + Q + 1) ^ 2) := by rw [hcast]; ring
      calc ∑ i ∈ Finset.range N, |b (i + Q)|
          ≤ ∑ i ∈ Finset.range N, C * (1 / ((i : ℝ) + Q + 1) ^ 2) :=
            Finset.sum_le_sum (fun i _ => step i)
        _ = C * ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + Q + 1) ^ 2) := by
            rw [Finset.mul_sum]
        _ ≤ C * (1 / (Q : ℝ) - 1 / ((Q : ℝ) + N)) := by
            exact mul_le_mul_of_nonneg_left (sum_inv_sq_shift_le Q hQ N) hC
        _ ≤ C / (Q : ℝ) := by
            have h0 : (0:ℝ) ≤ 1 / ((Q : ℝ) + N) := by positivity
            have := mul_nonneg hC h0
            rw [mul_sub, div_eq_mul_one_div C ((Q : ℝ))]
            linarith
    have : |(∑' i, b i) - ∑ i ∈ Finset.range Q, b i| ≤ C / (Q : ℝ) := by
      rw [htail]; exact le_trans habs hbound
    simpa [singularPartial_eq_range a, hb] using this

/-- A concrete instance: the Möbius-weighted singular series `∑_{q ≥ 1} μ(q) / q ^ 2`
converges, with effective truncation error at most `1 / Q`. -/
theorem SingularSeriesConvergenceRate_moebius :
    ∃ S : ℝ,
      Tendsto
        (fun Q => singularPartial
          (fun q => (ArithmeticFunction.moebius q : ℝ) / (q : ℝ) ^ 2) Q) atTop (nhds S) ∧
      ∀ Q : ℕ, 1 ≤ Q →
        |S - singularPartial
          (fun q => (ArithmeticFunction.moebius q : ℝ) / (q : ℝ) ^ 2) Q| ≤ 1 / (Q : ℝ) := by
  refine SingularSeriesConvergenceRate (C := 1) ?_
  intro q _
  have hmu : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    have : |ArithmeticFunction.moebius q| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
    exact_mod_cast this
  rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (q : ℝ) ^ 2)]
  gcongr

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

