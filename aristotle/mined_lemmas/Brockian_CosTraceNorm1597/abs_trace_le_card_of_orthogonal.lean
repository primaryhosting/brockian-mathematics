import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Brockian

open Matrix

/-- The planar rotation matrix by angle `θ`. -/

lemma abs_trace_le_card_of_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (h : Aᵀ * A = 1) : |A.trace| ≤ (Fintype.card n : ℝ) := by
  calc |A.trace| = |∑ i, A i i| := rfl
    _ ≤ ∑ i, |A i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => abs_diag_le_one_of_orthogonal A h i
    _ = (Fintype.card n : ℝ) := by simp [Finset.card_univ]

/-- The rotation matrix is orthogonal. -/
