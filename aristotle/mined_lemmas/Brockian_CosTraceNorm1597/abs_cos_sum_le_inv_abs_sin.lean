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
