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

theorem not_solvable_by_rad_quinticPhi (p : ℕ) (x : ℂ) (hx : aeval x (quinticPhi ℚ a b) = 0)
    (hab : b < a) (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) :
    ¬IsSolvableByRad ℚ x := by
  have h_irred := irreducible_quinticPhi a b p hp hpa hpb hp2b
  exact mt (solvableByRad.isSolvable' h_irred hx)
    (not_solvable_gal_quinticPhi a b p hab hp hpa hpb hp2b)

/-- **Abel–Ruffini in degree 5**: there is a monic irreducible quintic over `ℚ` whose Galois
group is not solvable, so that none of its (complex) roots is expressible by radicals; in
particular the general quintic equation is not solvable by radicals. -/
