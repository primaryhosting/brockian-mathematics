/- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`, so the
requested header is reproduced verbatim as a block comment here, and again as the module
docstring immediately after the import.)

# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

/-!
The development below is adapted from the Mathlib archive file
`Archive/Wiedijk100Theorems/AbelRuffini.lean` (Thomas Browning, Apache 2.0), which is not
importable from this project, and follows the classical Galois-theoretic proof of the Abel–Ruffini

theorem not_solvable_gal_quinticPhi (p : ℕ) (hab : b < a) (hp : p.Prime) (hpa : p ∣ a)
    (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) : ¬ IsSolvable (quinticPhi ℚ a b).Gal := by
  have h_irred := irreducible_quinticPhi a b p hp hpa hpb hp2b
  intro h
  refine Equiv.Perm.not_solvable _ (le_of_eq ?_)
    (solvable_of_surjective (gal_quinticPhi a b hab h_irred).2)
  rw_mod_cast [Cardinal.mk_fintype, complex_roots_quinticPhi a b h_irred.separable]

