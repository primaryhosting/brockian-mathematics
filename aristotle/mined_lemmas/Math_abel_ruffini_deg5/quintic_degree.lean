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

theorem quintic_degree : quintic.degree = 5 := by
  rw [quintic_eq]
  exact_mod_cast AbelRuffini.degree_Phi 4 2

