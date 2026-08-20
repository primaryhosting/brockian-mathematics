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

theorem exists_not_solvable_by_rad : ∃ x : ℂ, IsAlgebraic ℚ x ∧ ¬IsSolvableByRad ℚ x := by
  obtain ⟨x, hx⟩ := (IsAlgClosed.splits (Φ ℂ 4 2)).exists_eval_eq_zero (by simp [degree_Phi])
  rw [← map_Phi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
  exact ⟨x, ⟨Φ ℚ 4 2, (monic_Phi 4 2).ne_zero, hx⟩, not_solvable_by_rad' x hx⟩

end AbelRuffiniQuintic

import Mathlib
import RequestProject.AbelRuffiniAux

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

open Polynomial AbelRuffiniQuintic

/-- **Abel–Ruffini theorem** (Galois-theoretic form), for a specific quintic:
the polynomial `X ^ 5 - 4 * X + 2` over `ℚ` is irreducible of degree `5`,
its Galois group is not solvable, it has a root in `ℂ`, and none of its
complex roots is expressible by radicals over `ℚ`.
Hence the general quintic equation is not solvable by radicals. -/
