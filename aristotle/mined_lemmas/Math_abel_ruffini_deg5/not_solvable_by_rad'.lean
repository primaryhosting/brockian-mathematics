import Mathlib
/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/







/-!
# Construction of an algebraic number that is not solvable by radicals.

The main ingredients are:
* `solvableByRad.isSolvable'` in `Mathlib/FieldTheory/AbelRuffini.lean` :
  an irreducible polynomial with an `IsSolvableByRad` root has solvable Galois group
* `galActionHom_bijective_of_prime_degree'` in `Mathlib/FieldTheory/PolynomialGaloisGroup.lean` :
  an irreducible polynomial of prime degree with 1-3 non-real roots has full Galois group
* `Equiv.Perm.not_solvable` in `Mathlib/GroupTheory/Solvable.lean` : the symmetric group is not
  solvable

Then all that remains is the construction of a specific polynomial satisfying the conditions of
`galActionHom_bijective_of_prime_degree'`, which is done in this file.

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

theorem not_solvable_by_rad' (x : ℂ) (hx : aeval x (Φ ℚ 4 2) = 0) : ¬IsSolvableByRad ℚ x := by
  apply not_solvable_by_rad 4 2 2 x hx <;> decide

/-- **Abel-Ruffini Theorem** -/
