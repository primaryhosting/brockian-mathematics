/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Real MeasureTheory
open scoped Topology BigOperators Classical

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The Sato–Tate density `(2/π) sin²θ` on `[0, π]`. -/

lemma cos_mul_mem_USpan {g : ℝ → ℝ} (hg : g ∈ USpan) :
    (fun x => Real.cos x * g x) ∈ USpan := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨k, rfl⟩ := hg
      match k with
      | 0 =>
          have : (fun x => Real.cos x * UBasis 0 x) = (1/2 : ℝ) • UBasis 1 := by
            funext x
            simp [cos_mul_UBasis_zero x]
            ring
          rw [this]
          exact Submodule.smul_mem _ _ (UBasis_mem_USpan 1)
      | (j+1) =>
          have : (fun x => Real.cos x * UBasis (j + 1) x)
              = (1/2 : ℝ) • UBasis (j + 2) + (1/2 : ℝ) • UBasis j := by
            funext x
            simp [cos_mul_UBasis_succ j x]
            ring
          rw [this]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ (UBasis_mem_USpan (j + 2)))
            (Submodule.smul_mem _ _ (UBasis_mem_USpan j))
  | zero =>
      have : (fun x => Real.cos x * (0 : ℝ → ℝ) x) = 0 := by funext x; simp
      rw [this]
      exact Submodule.zero_mem _
  | add g h _ _ ih1 ih2 =>
      have : (fun x => Real.cos x * (g + h) x)
          = (fun x => Real.cos x * g x) + (fun x => Real.cos x * h x) := by
        funext x; simp [mul_add]
      rw [this]
      exact Submodule.add_mem _ ih1 ih2
  | smul c g _ ih =>
      have : (fun x => Real.cos x * (c • g) x) = c • (fun x => Real.cos x * g x) := by
        funext x; simp [mul_comm, mul_assoc]
      rw [this]
      exact Submodule.smul_mem _ _ ih

