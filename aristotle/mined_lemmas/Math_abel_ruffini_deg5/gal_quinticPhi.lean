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

theorem gal_quinticPhi (hab : b < a) (h_irred : Irreducible (quinticPhi ℚ a b)) :
    Bijective (galActionHom (quinticPhi ℚ a b) ℂ) := by
  apply galActionHom_bijective_of_prime_degree' h_irred
  · simp only [natDegree_quinticPhi]; decide
  · rw [complex_roots_quinticPhi a b h_irred.separable, Nat.succ_le_succ_iff]
    exact (real_roots_quinticPhi_le a b).trans (Nat.le_succ 3)
  · simp_rw [complex_roots_quinticPhi a b h_irred.separable, Nat.succ_le_succ_iff]
    exact real_roots_quinticPhi_ge a b hab

/-- The Galois group of the quintic `X ^ 5 - a * X + b` (for suitable `a`, `b`) is not
solvable: it is the full symmetric group on the five complex roots. -/
