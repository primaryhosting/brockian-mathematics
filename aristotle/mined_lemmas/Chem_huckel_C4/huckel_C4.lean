import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₄` (the Hückel matrix of cyclobutadiene,
with `α = 0`, `β = 1`): vertices are `Fin 4` arranged in a cycle, and `i ~ j` iff
`j = i + 1` or `i = j + 1` (addition modulo `4`). -/

theorem huckel_C4 (μ : ℝ) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4adj *ᵥ v = μ • v) ↔
      ∃ k : Fin 4, μ = 2 * Real.cos (2 * π * k / 4) := by
  rw [eigen_iff_det, cos_values]
  constructor
  · intro h
    have h' : μ ^ 2 * ((μ - 2) * (μ + 2)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact Or.inr (Or.inl (by simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1))
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num

end Chem

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

