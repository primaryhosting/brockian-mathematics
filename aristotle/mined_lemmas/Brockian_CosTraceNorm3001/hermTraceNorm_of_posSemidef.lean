import Mathlib

/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The cosine matrix associated to a family of phases `θ`: its `(i, j)` entry is
`cos (θ i - θ j)`. -/

lemma hermTraceNorm_of_posSemidef {A : Matrix n n ℝ} (h : A.PosSemidef) :
    hermTraceNorm A = A.trace := by
  rw [hermTraceNorm_of_isHermitian h.isHermitian]
  have hval : ∀ i, |h.isHermitian.eigenvalues i| = h.isHermitian.eigenvalues i := fun i =>
    abs_of_nonneg (h.eigenvalues_nonneg i)
  simp only [hval]
  rw [h.isHermitian.trace_eq_sum_eigenvalues (𝕜 := ℝ)]
  simp

omit [Fintype n] [DecidableEq n] in
/-- The cosine matrix is symmetric. -/
