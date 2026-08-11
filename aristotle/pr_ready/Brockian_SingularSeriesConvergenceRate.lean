/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open Finset

namespace Brockian

/-- The comparison series `q ↦ C / q ^ 2` used to control a singular series. -/
lemma summable_const_div_sq (C : ℝ) : Summable (fun q : ℕ => C / (q : ℝ) ^ 2) := by
  have h : Summable (fun q : ℕ => (1 : ℝ) / (q : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  simpa [div_eq_mul_inv, mul_comm] using h.mul_left C

/-- Tail estimate for the comparison series: for `1 ≤ N`, every partial sum of
`i ↦ C / (i + N) ^ 2` is at most `2 * C / N`. -/
lemma sum_range_shift_inv_sq_le {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    ∑ i ∈ range n, C / ((i : ℝ) + N) ^ 2 ≤ 2 * C / N := by
  have hcast : ∀ i ∈ range n, C / ((i : ℝ) + N) ^ 2 = C * (((N + i : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro i _
    push_cast
    rw [div_eq_mul_inv, add_comm (N : ℝ) (i : ℝ)]
  rw [Finset.sum_congr rfl hcast, ← Finset.mul_sum]
  have hIco : ∑ i ∈ range n, (((N + i : ℕ) : ℝ) ^ 2)⁻¹
      = ∑ j ∈ Finset.Ico N (N + n), (((j : ℕ) : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  have hsub : Finset.Ico N (N + n) ⊆ Finset.Ioo (N - 1) (N + n) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    simp only [Finset.mem_Ioo]
    exact ⟨by omega, hj.2⟩
  have hnn : ∀ j ∈ Finset.Ioo (N - 1) (N + n), j ∉ Finset.Ico N (N + n) →
      (0 : ℝ) ≤ (((j : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro j _ _
    positivity
  have h1 : ∑ j ∈ Finset.Ico N (N + n), (((j : ℕ) : ℝ) ^ 2)⁻¹
      ≤ ∑ j ∈ Finset.Ioo (N - 1) (N + n), (((j : ℕ) : ℝ) ^ 2)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have h2 : ∑ j ∈ Finset.Ioo (N - 1) (N + n), (((j : ℕ) : ℝ) ^ 2)⁻¹
      ≤ 2 / (((N - 1 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le (N - 1) (N + n)
  have hcast2 : (((N - 1 : ℕ) : ℝ) + 1) = (N : ℝ) := by
    have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      have := Nat.cast_sub (R := ℝ) hN
      simpa using this
    rw [this]; ring
  rw [hcast2] at h2
  calc C * ∑ i ∈ range n, (((N + i : ℕ) : ℝ) ^ 2)⁻¹
      = C * ∑ j ∈ Finset.Ico N (N + n), (((j : ℕ) : ℝ) ^ 2)⁻¹ := by rw [hIco]
    _ ≤ C * (2 / (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (h1.trans h2) hC
    _ = 2 * C / N := by ring

/--
**Singular series convergence rate.**

If the terms `a q` of a series (e.g. the local densities making up a Hardy–Littlewood
singular series) satisfy the effective bound `|a q| ≤ C / q ^ 2` for all `q ≥ 1`, then the
series converges and its truncation at level `N` approximates the full sum with the
effective error bound `2 * C / N`.
-/
theorem SingularSeriesConvergenceRate {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ q : ℕ, 1 ≤ q → |a q| ≤ C / (q : ℝ) ^ 2) :
    Summable a ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑' q, a q) - ∑ q ∈ range N, a q| ≤ 2 * C / N := by
  -- The constant is necessarily nonnegative.
  have hC : 0 ≤ C := by
    have := ha 1 le_rfl
    have h0 : (0 : ℝ) ≤ |a 1| := abs_nonneg _
    simpa using h0.trans this
  -- Summability of `|a|`, hence of `a`.
  have habs : Summable (fun q : ℕ => |a q|) := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun i => abs_nonneg _) (fun i => ha (i + 1) (by omega))
      ?_
    exact (summable_nat_add_iff (f := fun q : ℕ => C / (q : ℝ) ^ 2) 1).mpr
      (summable_const_div_sq C)
  have hsum : Summable a := by
    simpa using habs.of_abs
  refine ⟨hsum, ?_⟩
  intro N hN
  -- Split off the first `N` terms.
  have hsplit := hsum.sum_add_tsum_nat_add (f := a) N
  have hrewrite : (∑' q, a q) - ∑ q ∈ range N, a q = ∑' i : ℕ, a (i + N) := by
    rw [← hsplit]; ring
  rw [hrewrite]
  -- Bound the tail by the tail of the comparison series.
  have hshift : Summable (fun i : ℕ => |a (i + N)|) :=
    (summable_nat_add_iff (f := fun q : ℕ => |a q|) N).mpr habs
  have hpartial : ∀ n : ℕ, ∑ i ∈ range n, |a (i + N)| ≤ 2 * C / N := by
    intro n
    refine le_trans (Finset.sum_le_sum ?_) (sum_range_shift_inv_sq_le hC hN n)
    intro i _
    have := ha (i + N) (by omega)
    calc |a (i + N)| ≤ C / (((i + N : ℕ) : ℝ)) ^ 2 := this
      _ = C / ((i : ℝ) + N) ^ 2 := by push_cast; ring_nf
  have h1 : |∑' i : ℕ, a (i + N)| ≤ ∑' i : ℕ, |a (i + N)| := by
    have := norm_tsum_le_tsum_norm (f := fun i : ℕ => a (i + N))
      (by simpa [Real.norm_eq_abs] using hshift)
    simpa [Real.norm_eq_abs] using this
  have h2 : ∑' i : ℕ, |a (i + N)| ≤ 2 * C / N :=
    Real.tsum_le_of_sum_range_le (fun i => abs_nonneg _) hpartial
  exact h1.trans h2

end Brockian


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

