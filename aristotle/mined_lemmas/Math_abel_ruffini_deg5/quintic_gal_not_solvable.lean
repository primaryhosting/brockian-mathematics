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

theorem quintic_gal_not_solvable : ¬ IsSolvable quintic.Gal := by
  rw [quintic_eq]
  have h_irred :=
    AbelRuffini.irreducible_Phi 4 2 2 (by norm_num) (by norm_num) (by norm_num) (by decide)
  intro h
  refine Equiv.Perm.not_solvable _ (le_of_eq ?_)
    (solvable_of_surjective (AbelRuffini.gal_Phi 4 2 (by norm_num) h_irred).2)
  rw_mod_cast [Cardinal.mk_fintype,
    AbelRuffini.complex_roots_Phi 4 2 h_irred.separable]

/-- **Abel–Ruffini for the quintic.**  There is a monic irreducible quintic over `ℚ` whose
Galois group is not solvable and which has a complex root that is not expressible by radicals;
hence the general quintic equation is not solvable by radicals.

The construction and the key ingredients come from Mathlib
(`Mathlib/FieldTheory/AbelRuffini.lean`, `Archive/Wiedijk100Theorems/AbelRuffini.lean`). -/
