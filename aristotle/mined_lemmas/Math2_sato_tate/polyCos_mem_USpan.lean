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

lemma polyCos_mem_USpan (P : Polynomial ℝ) :
    (fun x : ℝ => P.eval (Real.cos x)) ∈ USpan := by
  have hrw : (fun x : ℝ => P.eval (Real.cos x))
      = ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i) • (fun x : ℝ => Real.cos x ^ i) := by
    funext x
    rw [Polynomial.eval_eq_sum_range]
    simp [Finset.sum_apply]
  rw [hrw]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (cos_pow_mem_USpan i))

