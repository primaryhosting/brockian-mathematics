import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module doc comment, so the header
-- block above sits immediately after the single `import Mathlib` line.)

open scoped BigOperators
open scoped Real
open scoped Matrix

set_option maxRecDepth 10000

namespace Brockian

/-- The cosine kernel matrix `C i j = cos (x i - x j)` attached to a family of phases `x`. -/

theorem cos_kernel_quadratic_form (n : ℕ) (x v : Fin n → ℝ) :
    ∑ i, ∑ j, v i * v j * Real.cos (x i - x j)
      = (∑ i, v i * Real.cos (x i)) ^ 2 + (∑ i, v i * Real.sin (x i)) ^ 2 := by
  have hc : (∑ i, v i * Real.cos (x i)) ^ 2
      = ∑ i, ∑ j, (v i * Real.cos (x i)) * (v j * Real.cos (x j)) := by
    rw [sq, Finset.sum_mul_sum]
  have hs : (∑ i, v i * Real.sin (x i)) ^ 2
      = ∑ i, ∑ j, (v i * Real.sin (x i)) * (v j * Real.sin (x j)) := by
    rw [sq, Finset.sum_mul_sum]
  rw [hc, hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.cos_sub]
  ring

/-- The bilinear pairing `⟪v, C v⟫` written out as a double sum. -/
