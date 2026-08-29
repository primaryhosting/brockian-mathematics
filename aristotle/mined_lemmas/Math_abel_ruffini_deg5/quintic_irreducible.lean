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

theorem quintic_irreducible : Irreducible quintic := by
  rw [quintic_eq]
  exact AbelRuffini.irreducible_Phi 4 2 2 (by norm_num) (by norm_num) (by norm_num) (by decide)

