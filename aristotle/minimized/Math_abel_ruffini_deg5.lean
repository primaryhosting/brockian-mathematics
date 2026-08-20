/-
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Archive.Wiedijk100Theorems.AbelRuffini

/-!
# Abel Ruffini Deg 5

The quintic is not solvable by radicals: there is a degree-`5` irreducible polynomial over `ℚ`
whose Galois group is not solvable (indeed its Galois group acts on the five complex roots as the
full symmetric group `S₅`), and hence none of whose complex roots is expressible by radicals.

The witness is `X ^ 5 - 4 * X + 2`, which is Eisenstein at `2` and has exactly three real roots.

The main input is Mathlib's Archive development of the Abel-Ruffini theorem
(`Archive/Wiedijk100Theorems/AbelRuffini.lean`, by Thomas Browning), which provides
`AbelRuffini.gal_Phi`, `AbelRuffini.irreducible_Phi` and `AbelRuffini.complex_roots_Phi`,
together with `solvableByRad.isSolvable'` and `Equiv.Perm.not_solvable` from Mathlib proper.
-/

namespace Math

open Polynomial

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- The witness polynomial `X ^ 5 - 4 * X + 2 : ℚ[X]`. -/
noncomputable def quinticWitness : ℚ[X] := X ^ 5 - C 4 * X + C 2

theorem quinticWitness_eq : quinticWitness = AbelRuffini.Φ ℚ 4 2 := by
  simp [quinticWitness, AbelRuffini.Φ]

/-- **Abel-Ruffini theorem in degree 5.** The general quintic is not solvable by radicals:
the irreducible rational quintic `X ^ 5 - 4 * X + 2` has non-solvable Galois group (its Galois
group acts on the five complex roots as the full symmetric group), and consequently none of its
complex roots -- which exist -- is solvable by radicals over `ℚ`. -/
theorem abel_ruffini_deg5 :
    ∃ p : ℚ[X], p.natDegree = 5 ∧ Irreducible p ∧
      Function.Bijective (Gal.galActionHom p ℂ) ∧
      ¬ IsSolvable p.Gal ∧
      (∃ x : ℂ, aeval x p = 0) ∧
      (∀ x : ℂ, aeval x p = 0 → ¬ IsSolvableByRad ℚ x) := by
  refine ⟨quinticWitness, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [quinticWitness_eq]; exact AbelRuffini.natDegree_Phi 4 2
  · rw [quinticWitness_eq]
    exact AbelRuffini.irreducible_Phi 4 2 2 Nat.prime_two (by norm_num) (by norm_num) (by norm_num)
  · rw [quinticWitness_eq]
    exact AbelRuffini.gal_Phi 4 2 (by norm_num)
      (AbelRuffini.irreducible_Phi 4 2 2 Nat.prime_two (by norm_num) (by norm_num) (by norm_num))
  · rw [quinticWitness_eq]
    have h_irred := AbelRuffini.irreducible_Phi 4 2 2 Nat.prime_two (by norm_num) (by norm_num) (by norm_num)
    intro h
    refine Equiv.Perm.not_solvable _ (le_of_eq ?_)
      (solvable_of_surjective (AbelRuffini.gal_Phi 4 2 (by norm_num) h_irred).2)
    rw_mod_cast [Cardinal.mk_fintype, AbelRuffini.complex_roots_Phi 4 2 h_irred.separable]
  · obtain ⟨x, hx⟩ := (IsAlgClosed.splits (AbelRuffini.Φ ℂ 4 2)).exists_eval_eq_zero
      (by simp [AbelRuffini.degree_Phi])
    rw [← AbelRuffini.map_Phi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
    exact ⟨x, by rwa [quinticWitness_eq]⟩
  · intro x hx
    rw [quinticWitness_eq] at hx
    exact AbelRuffini.not_solvable_by_rad' x hx

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

