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

theorem not_solvable_gal_Phi (p : ℕ) (hab : b < a)
    (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) :
    ¬ IsSolvable (Phi ℚ a b).Gal := by
  have h_irred := irreducible_Phi a b p hp hpa hpb hp2b
  intro h
  refine Equiv.Perm.not_solvable _ (le_of_eq ?_)
    (solvable_of_surjective (gal_Phi a b hab h_irred).2)
  rw_mod_cast [Cardinal.mk_fintype, complex_roots_Phi a b h_irred.separable]

