/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The `n × n` real "cosine Hankel" matrix with entries `cos (θ * (i + j))`. -/
noncomputable def cosMatrix (θ : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (θ * (i.val + j.val))

/-- The trace of `cosMatrix θ n` is the cosine sum `∑_{k<n} cos (2θk)`. -/
lemma trace_cosMatrix (θ : ℝ) (n : ℕ) :
    Matrix.trace (cosMatrix θ n) = ∑ k ∈ Finset.range n, Real.cos (2 * θ * k) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => Real.cos (2 * θ * k)) n, Matrix.trace]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Matrix.diag_apply, cosMatrix, Matrix.of_apply]
  ring_nf

/-- Telescoping identity: `sin θ · ∑_{k<n} cos (2θk) = (sin ((2n-1)θ) + sin θ)/2`. -/
lemma sin_mul_cos_sum (θ : ℝ) (n : ℕ) :
    Real.sin θ * ∑ k ∈ Finset.range n, Real.cos (2 * θ * k)
      = (Real.sin ((2 * n - 1) * θ) + Real.sin θ) / 2 := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, Nat.cast_zero]
      rw [show (((0 : ℝ) - 1) * θ) = -θ by ring, Real.sin_neg]
      ring
  | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have h1 : ((2 * (m + 1 : ℕ) : ℝ) - 1) * θ = 2 * m * θ + θ := by
        push_cast; ring
      have h2 : ((2 * (m : ℕ) : ℝ) - 1) * θ = 2 * m * θ - θ := by ring
      rw [h1, h2, Real.sin_add, Real.sin_sub]
      have : Real.sin θ * Real.cos (2 * θ * m) = Real.sin θ * Real.cos (2 * m * θ) := by
        ring_nf
      rw [this]
      ring

/-- Trivial bound: the cosine sum is bounded by the number of terms. -/
lemma abs_cos_sum_le_card (θ : ℝ) (n : ℕ) :
    |∑ k ∈ Finset.range n, Real.cos (2 * θ * k)| ≤ n := by
  calc |∑ k ∈ Finset.range n, Real.cos (2 * θ * k)|
      ≤ ∑ k ∈ Finset.range n, |Real.cos (2 * θ * k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro k _
        exact Real.abs_cos_le_one _
    _ = n := by simp

/-- Dirichlet-type bound: away from the zeros of `sin`, the cosine sum is bounded by
`1 / |sin θ|`, uniformly in the number of terms. -/
lemma abs_cos_sum_le_inv_abs_sin (θ : ℝ) (n : ℕ) (hθ : Real.sin θ ≠ 0) :
    |∑ k ∈ Finset.range n, Real.cos (2 * θ * k)| ≤ 1 / |Real.sin θ| := by
  have key := sin_mul_cos_sum θ n
  have habs : |Real.sin θ| * |∑ k ∈ Finset.range n, Real.cos (2 * θ * k)| ≤ 1 := by
    rw [← abs_mul, key]
    have h1 : |Real.sin ((2 * (n : ℝ) - 1) * θ)| ≤ 1 := Real.abs_sin_le_one _
    have h2 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one _
    have := abs_add_le (Real.sin ((2 * (n : ℝ) - 1) * θ)) (Real.sin θ)
    rw [abs_div]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    linarith
  have hpos : 0 < |Real.sin θ| := abs_pos.mpr hθ
  rw [le_div_iff₀ hpos]
  linarith [habs]

/--
**Cos Trace Norm 1597.**

For the `1597 × 1597` cosine Hankel matrix `cosMatrix θ 1597` with entries `cos (θ (i+j))`,
its trace is the cosine sum `∑_{k<1597} cos (2θk)`; it satisfies the trivial bound `1597`,
the Dirichlet-type bound `1 / |sin θ|` away from the zeros of `sin`, and attains the value
`1597` at `θ = 0`.
-/
theorem CosTraceNorm1597 :
    (∀ θ : ℝ, Matrix.trace (cosMatrix θ 1597)
        = ∑ k ∈ Finset.range 1597, Real.cos (2 * θ * k)) ∧
    (∀ θ : ℝ, |Matrix.trace (cosMatrix θ 1597)| ≤ 1597) ∧
    (∀ θ : ℝ, Real.sin θ ≠ 0 →
        |Matrix.trace (cosMatrix θ 1597)| ≤ 1 / |Real.sin θ|) ∧
    Matrix.trace (cosMatrix 0 1597) = 1597 := by
  refine ⟨fun θ => trace_cosMatrix θ 1597, fun θ => ?_, fun θ hθ => ?_, ?_⟩
  · rw [trace_cosMatrix]
    simpa using abs_cos_sum_le_card θ 1597
  · rw [trace_cosMatrix]
    exact abs_cos_sum_le_inv_abs_sin θ 1597 hθ
  · rw [trace_cosMatrix]
    simp

end Brockian

