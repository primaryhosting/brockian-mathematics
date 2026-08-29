/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- `countUpTo A N` is the number of elements of `A` below `N`. -/

theorem infinite_of_upperDensity_pos (A : Set ℕ) (h : 0 < upperDensity A) : A.Infinite := by
  obtain ⟨δ, hδ, hwin⟩ := exists_density_windows A h
  by_contra hfin
  rw [Set.not_infinite] at hfin
  set c : ℕ := hfin.toFinset.card with hcdef
  have hbound : ∀ N : ℕ, countUpTo A N ≤ c := by
    intro N
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    exact hfin.mem_toFinset.mpr hx.2
  obtain ⟨M, hM⟩ := exists_nat_gt (((c : ℝ) + 1) / δ)
  obtain ⟨N, hNM, hN⟩ := hwin M
  have hMN : ((c : ℝ) + 1) / δ < (N : ℝ) := lt_of_lt_of_le hM (by exact_mod_cast hNM)
  have h1 : (c : ℝ) + 1 < δ * N := by
    rw [div_lt_iff₀ hδ] at hMN; linarith
  have h2 : (countUpTo A N : ℝ) ≤ (c : ℝ) := by exact_mod_cast hbound N
  linarith

/-- The finitary Szemerédi statement is unconditionally true for progression lengths
`k ≤ 2`: a subset of `{0, …, N-1}` of size at least `δ N` with `N` large has two distinct
elements, hence a two-term progression. -/
