/-
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment; the same text is repeated as a module docstring below.)

import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Polynomial
open scoped Classical

set_option maxHeartbeats 1000000

namespace AbelRuffiniQuintic

open Function Polynomial Polynomial.Gal Ideal

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- The quintic `X ^ 5 - a * X + b`, which for suitable `a, b` is irreducible over `ℚ`
with Galois group `S₅`. -/

noncomputable def Phi : R[X] :=
  X ^ 5 - C (a : R) * X + C (b : R)

variable {R}

@[simp]
