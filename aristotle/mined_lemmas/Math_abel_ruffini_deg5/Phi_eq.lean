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

theorem Phi_eq : Φ ℚ 4 2 = X ^ 5 - C 4 * X + C 2 := by
  norm_num [Φ]

end AbelRuffiniQuintic

open Polynomial in
/-- **Abel–Ruffini theorem, quintic case.**  The quintic `X ^ 5 - 4 * X + 2` over `ℚ` is monic,
of degree `5`, irreducible, has non-solvable Galois group, has a complex root, and *none* of its
complex roots is expressible by radicals over `ℚ`.  In particular the general quintic equation is
not solvable by radicals. -/
