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

set_option grind.warning false

/-!
# Hückel theory for the cycle graph `C₃`

The adjacency eigenvalues of the cycle graph `C₃` (the carbon skeleton of a three-membered
conjugated ring, in Hückel theory) are exactly the numbers `2 * cos (2 * π * k / 3)` for
`k = 0, 1, 2`.

The main statement `Chem.huckel_C3` says that a real number `μ` is an eigenvalue of the
adjacency matrix of `SimpleGraph.cycleGraph 3` (i.e. there is a nonzero vector `v` with
`A *ᵥ v = μ • v`) if and only if `μ = 2 * cos (2 * π * k / 3)` for some `k : Fin 3`.

`Chem.huckel_C3_charpoly` records the stronger, multiplicity-aware version: the characteristic
polynomial of the adjacency matrix is `∏ k : Fin 3, (X - C (2 * cos (2 * π * k / 3)))`.
-/

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₃`, over `ℝ`. -/

theorem two_cos_range (μ : ℝ) :
    (∃ k : Fin 3, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3)) ↔ (μ = 2 ∨ μ = -1) := by
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl two_cos_zero
    · exact Or.inr two_cos_one
    · exact Or.inr two_cos_two
  · rintro (rfl | rfl)
    · exact ⟨0, two_cos_zero.symm⟩
    · exact ⟨1, two_cos_one.symm⟩

/-- The real eigenvalues of the adjacency matrix of `C₃` are exactly `2` and `-1`. -/
