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

def IsRatPt (x : ℂ) : Prop := ∃ q : ℚ, algebraMap ℚ ℂ q = x

/-- The degree over `ℚ` of an algebraic number. -/
