/-
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`, so the header
-- above is a plain comment and is repeated verbatim as a module docstring after the import.)

/-
The argument below is the classical Galois-theoretic proof of the Abel-Ruffini theorem
in degree 5, following the treatment of `Archive/Wiedijk100Theorems/AbelRuffini.lean`
in mathlib4 (author: Thomas Browning, Apache 2.0).  It is reproduced here in
self-contained form because the mathlib `Archive` library is not imported by default.

The key mathlib ingredients are:
* `solvableByRad.isSolvable'`  (an irreducible polynomial with a root solvable by radicals
  has solvable Galois group);
* `Polynomial.Gal.galActionHom_bijective_of_prime_degree'`  (an irreducible polynomial of
  prime degree with 1-3 non-real roots has full Galois group);
* `Equiv.Perm.not_solvable`  (the symmetric group on 5 letters is not solvable).
-/

import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

namespace AbelRuffiniQuintic

open Function Polynomial Polynomial.Gal Ideal

open scoped Polynomial

attribute [local instance] splits_ℚ_ℂ

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- The quintic `X ^ 5 - a * X + b`. -/

theorem gal_Phi (hab : b < a) (h_irred : Irreducible (Phi ℚ a b)) :
    Bijective (galActionHom (Phi ℚ a b) ℂ) := by
  apply galActionHom_bijective_of_prime_degree' h_irred
  · simp only [natDegree_Phi]; decide
  · rw [complex_roots_Phi a b h_irred.separable, Nat.succ_le_succ_iff]
    exact (real_roots_Phi_le a b).trans (Nat.le_succ 3)
  · simp_rw [complex_roots_Phi a b h_irred.separable, Nat.succ_le_succ_iff]
    exact real_roots_Phi_ge a b hab

/-- The Galois group of `X ^ 5 - a * X + b` (for suitable `a`, `b`) is not solvable. -/
