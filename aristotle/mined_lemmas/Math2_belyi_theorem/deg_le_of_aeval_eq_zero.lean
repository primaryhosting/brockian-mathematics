import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

open Polynomial IntermediateField

namespace Math2

/-- A complex number is a *rational point* if it lies in the image of `ℚ`. -/

lemma deg_le_of_aeval_eq_zero {q : ℚ[X]} (hq : q ≠ 0) {c : ℂ} (h : aeval c q = 0) :
    deg c ≤ q.natDegree := by
  have hm : (q * C (q.leadingCoeff)⁻¹).Monic := monic_mul_leadingCoeff_inv hq
  have h0 : aeval c (q * C (q.leadingCoeff)⁻¹) = 0 := by simp [h]
  have hmin := minpoly.min ℚ c hm h0
  have hd : (q * C (q.leadingCoeff)⁻¹).natDegree = q.natDegree := by
    simp [natDegree_mul_leadingCoeff_inv, hq]
  exact (natDegree_le_natDegree hmin).trans_eq hd

/-! ### Critical values of a composition -/

