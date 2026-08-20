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

lemma isRatPt_of_deg_le_one {x : ℂ} (hx : IsIntegral ℚ x) (h : deg x ≤ 1) : IsRatPt x := by
  have h1 : deg x = 1 := le_antisymm h (deg_pos hx)
  obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.1 h1
  exact ⟨q, hq⟩

