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

theorem Math.abel_ruffini_deg5 :
    ∃ p : ℚ[X], p = X ^ 5 - C 4 * X + C 2 ∧ p.Monic ∧ p.degree = 5 ∧ Irreducible p ∧
      ¬ IsSolvable p.Gal ∧ (∃ x : ℂ, aeval x p = 0) ∧
      ∀ x : ℂ, aeval x p = 0 → ¬ IsSolvableByRad ℚ x := by
  refine ⟨AbelRuffiniQuintic.Φ ℚ 4 2, AbelRuffiniQuintic.Phi_eq, AbelRuffiniQuintic.monic_Phi 4 2,
    ?_, AbelRuffiniQuintic.irreducible_Phi 4 2 2 (by norm_num) (by norm_num) (by norm_num)
      (by decide), AbelRuffiniQuintic.gal_not_solvable_Phi, ?_,
    fun x hx => AbelRuffiniQuintic.not_solvable_by_rad' x hx⟩
  · simpa using AbelRuffiniQuintic.degree_Phi (R := ℚ) 4 2
  · obtain ⟨x, hx⟩ := (IsAlgClosed.splits (AbelRuffiniQuintic.Φ ℂ 4 2)).exists_eval_eq_zero
      (by simp [AbelRuffiniQuintic.degree_Phi])
    rw [← AbelRuffiniQuintic.map_Phi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
    exact ⟨x, hx⟩

import Mathlib

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

