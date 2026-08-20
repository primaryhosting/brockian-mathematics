/- (module docstrings may not precede `import`, so the required header is kept
   verbatim inside this comment block)
/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Brockian

/-- The cosine Gram matrix of a family of angles: `C i j = cos (x i - x j)`.
It is the Gram matrix of the unit vectors `(cos (x i), sin (x i))`, hence positive
semidefinite of rank at most `2`. -/

lemma abs_quadratic_le_of_contraction {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : ∀ w : Fin n → ℝ, ∑ i, (∑ j, U i j * w j) ^ 2 ≤ ∑ i, (w i) ^ 2)
    (u : Fin n → ℝ) :
    |∑ j, u j * ∑ i, U j i * u i| ≤ ∑ i, (u i) ^ 2 := by
  set A : ℝ := ∑ i, (u i) ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hCS : (∑ j, u j * ∑ i, U j i * u i) ^ 2 ≤ A * ∑ j, (∑ i, U j i * u i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hUu : ∑ j, (∑ i, U j i * u i) ^ 2 ≤ A := hU u
  have hsq : (∑ j, u j * ∑ i, U j i * u i) ^ 2 ≤ A ^ 2 := by
    have := mul_le_mul_of_nonneg_left hUu hA0
    nlinarith [hCS]
  rw [abs_le]
  constructor <;> nlinarith [hsq, hA0]

/-- The trace of the cosine Gram matrix is `n`. -/
