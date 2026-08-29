/-
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The construction of the quintic `Φ R a b = X^5 - C a * X + C b` and the supporting lemmas below
are adapted from Mathlib's Archive file `Archive/Wiedijk100Theorems/AbelRuffini.lean`
(author: Thomas Browning, Apache 2.0 license).  They are reproduced here because the Archive is
not part of the `Mathlib` library target and hence cannot be imported.
-/
import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AbelRuffiniQuintic


open Function Polynomial Polynomial.Gal Ideal

open scoped Polynomial

attribute [local instance] splits_ℚ_ℂ

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- A quintic polynomial that we will show is irreducible -/
noncomputable def Φ : R[X] :=
  X ^ 5 - C (a : R) * X + C (b : R)

variable {R}

@[simp]

theorem leadingCoeff_Phi : (Φ R a b).leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, natDegree_Phi, coeff_five_Phi]

