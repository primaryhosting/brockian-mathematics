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

lemma belyiPoly_critval (a b : ℕ) {c : ℂ}
    (h : aeval c (derivative (belyiPoly a b)) = 0) :
    aeval c (belyiPoly a b) = 0 ∨ aeval c (belyiPoly a b) = 1 := by
  rcases belyiPoly_critical_points a b h with rfl | rfl | rfl
  · left; simp [belyiPoly]
  · left; simp [belyiPoly]
  · right; rw [aeval_ratPoint, belyiPoly_eval_crit, map_one]

/-- The sharp bound `xᵐ (1-x)ⁿ (m+n)^(m+n) ≤ mᵐ nⁿ` on `[0,1]` (weighted AM–GM). -/
