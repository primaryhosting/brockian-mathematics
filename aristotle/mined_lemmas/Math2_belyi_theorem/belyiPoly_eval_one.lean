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

lemma belyiPoly_eval_one (a b : ℕ) : (belyiPoly a b).eval 1 = 0 := by simp [belyiPoly]

/-- The unique interior critical point of the Belyi polynomial. -/
