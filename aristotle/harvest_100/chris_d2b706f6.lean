/-
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import Archive.Wiedijk100Theorems.AbelRuffini

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial

namespace Math

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- The witnessing quintic `X ^ 5 - 4 * X + 2` over `ℚ`. -/
noncomputable def quintic : ℚ[X] := X ^ 5 - C 4 * X + C 2

theorem quintic_eq : quintic = AbelRuffini.Φ ℚ 4 2 := by
  simp [quintic, AbelRuffini.Φ]

theorem quintic_irreducible : Irreducible quintic := by
  rw [quintic_eq]
  exact AbelRuffini.irreducible_Phi 4 2 2 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem quintic_degree : quintic.degree = 5 := by
  rw [quintic_eq]
  exact_mod_cast AbelRuffini.degree_Phi 4 2

theorem quintic_monic : quintic.Monic := by
  rw [quintic_eq]; exact AbelRuffini.monic_Phi 4 2

/-- The Galois group of `X ^ 5 - 4 * X + 2` over `ℚ` is not solvable. -/
theorem quintic_gal_not_solvable : ¬ IsSolvable quintic.Gal := by
  rw [quintic_eq]
  have h_irred :=
    AbelRuffini.irreducible_Phi 4 2 2 (by norm_num) (by norm_num) (by norm_num) (by decide)
  intro h
  refine Equiv.Perm.not_solvable _ (le_of_eq ?_)
    (solvable_of_surjective (AbelRuffini.gal_Phi 4 2 (by norm_num) h_irred).2)
  rw_mod_cast [Cardinal.mk_fintype,
    AbelRuffini.complex_roots_Phi 4 2 h_irred.separable]

/-- **Abel–Ruffini for the quintic.**  There is a monic irreducible quintic over `ℚ` whose
Galois group is not solvable and which has a complex root that is not expressible by radicals;
hence the general quintic equation is not solvable by radicals.

The construction and the key ingredients come from Mathlib
(`Mathlib/FieldTheory/AbelRuffini.lean`, `Archive/Wiedijk100Theorems/AbelRuffini.lean`). -/
theorem abel_ruffini_deg5 :
    ∃ p : ℚ[X], p.degree = 5 ∧ p.Monic ∧ Irreducible p ∧ ¬ IsSolvable p.Gal ∧
      ∃ x : ℂ, aeval x p = 0 ∧ ¬ IsSolvableByRad ℚ x := by
  refine ⟨quintic, quintic_degree, quintic_monic, quintic_irreducible,
    quintic_gal_not_solvable, ?_⟩
  obtain ⟨x, hx⟩ := (IsAlgClosed.splits (AbelRuffini.Φ ℂ 4 2)).exists_eval_eq_zero
    (by simp [AbelRuffini.degree_Phi])
  rw [← AbelRuffini.map_Phi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
  exact ⟨x, by rw [quintic_eq]; exact hx, AbelRuffini.not_solvable_by_rad' x hx⟩

end Math

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

