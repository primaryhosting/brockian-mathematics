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

noncomputable def belyiPoly (a b : ℕ) : ℚ[X] :=
  C (belyiConst a b) * (X ^ (a + 1) * (1 - X) ^ (b + 1))

