import RequestProject.CapExpand

/-!
# The Ellenberg–Gijswijt bound

Combining the slice-rank bound with the polynomial expansion gives
`|A| ≤ 3 · #{exponent vectors of degree ≤ 2n/3}` for every 3AP-free `A ⊆ 𝔽₃ⁿ`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- In `𝔽₃ⁿ`, a 3AP-free set contains no nontrivial triple summing to zero. -/

theorem capSetMax_isLittleO :
    (fun n => (capSetMax n : ℝ)) =o[Filter.atTop] (fun n => (3 : ℝ) ^ n) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := cap_set ε hε
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have hne : (capSets n).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [capSets, ThreeAPFree]
  obtain ⟨A, hAmem, hAeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  have hA : ThreeAPFree (A : Set (Fin n → ZMod 3)) := (mem_filter.mp hAmem).2
  have hbd := hN n hn A hA
  rw [capSetMax, hAeq, Real.norm_natCast,
    Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (3:ℝ) ^ n)]
  exact hbd

end Math2

import Mathlib

/-!
# Slice rank of the diagonal tensor

This file contains the linear-algebra core of the Croot–Lev–Pach / Ellenberg–Gijswijt
argument: if the diagonal tensor on a finite type `X` admits a decomposition into
`r₁ + r₂ + r₃` "slices", then `card X ≤ r₁ + r₂ + r₃`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

variable {F : Type*} [Field F] {X : Type*} [Fintype X] [DecidableEq X]

/-- The restriction of a submodule of functions `X → F` to a finset `S`. -/
