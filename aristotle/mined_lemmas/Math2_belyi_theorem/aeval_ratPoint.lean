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

lemma aeval_ratPoint (q : ℚ) (p : ℚ[X]) :
    aeval (algebraMap ℚ ℂ q) p = algebraMap ℚ ℂ (p.eval q) :=
  (Polynomial.aeval_algebraMap_apply _ _ _).trans (by simp)

/-- All critical values of the Belyi polynomial are `0` or `1`. -/
