/-
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import Archive.Wiedijk100Theorems.AbelRuffini

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial

namespace Math

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- The witnessing quintic `X ^ 5 - 4 * X + 2` over `ℚ`. -/

theorem quintic_monic : quintic.Monic := by
  rw [quintic_eq]; exact AbelRuffini.monic_Phi 4 2

/-- The Galois group of `X ^ 5 - 4 * X + 2` over `ℚ` is not solvable. -/
