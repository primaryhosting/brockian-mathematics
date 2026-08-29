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

lemma cos_pow_mem_USpan (m : ℕ) : (fun x : ℝ => Real.cos x ^ m) ∈ USpan := by
  induction m with
  | zero =>
      have : (fun x : ℝ => Real.cos x ^ 0) = UBasis 0 := by
        funext x; simp [UBasis_zero]
      rw [this]
      exact UBasis_mem_USpan 0
  | succ m ih =>
      have : (fun x : ℝ => Real.cos x ^ (m + 1)) = fun x => Real.cos x * Real.cos x ^ m := by
        funext x; ring
      rw [this]
      exact cos_mul_mem_USpan ih

