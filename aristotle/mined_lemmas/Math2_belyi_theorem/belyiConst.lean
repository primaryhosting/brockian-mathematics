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

noncomputable def belyiConst (a b : ℕ) : ℚ :=
  ((a + b + 2 : ℚ) ^ (a + b + 2)) / ((a + 1 : ℚ) ^ (a + 1) * (b + 1 : ℚ) ^ (b + 1))

/-- The normalised Belyi polynomial attached to `m = a+1`, `n = b+1`. -/
