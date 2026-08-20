/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is a plain block comment; its text is otherwise verbatim.)

import Mathlib

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `Fin 8` with cyclic
successor/predecessor. -/

theorem huckel_C8_spectrum (μ : ℂ) :
    (∃ v : Fin 8 → ℂ, v ≠ 0 ∧ C8adj.mulVec v = μ • v) ↔
      μ ∈ ({2, ((Real.sqrt 2 : ℝ) : ℂ), 0, -((Real.sqrt 2 : ℝ) : ℂ), -2} : Set ℂ) := by
  have hval : ∀ j : Fin 8, ((2 * Real.cos (2 * Real.pi * j / 8) : ℝ) : ℂ) = ((C8eig j : ℝ) : ℂ) :=
    fun _ => rfl
  rw [huckel_C8]
  constructor
  · rintro ⟨k, rfl⟩
    rw [hval k]
    rcases Fin8_cases k with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [C8eig_zero, C8eig_one, C8eig_two, C8eig_three, C8eig_four, C8eig_five,
        C8eig_six, C8eig_seven, Set.mem_insert_iff]
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h | h
    · exact ⟨0, by rw [h, hval, C8eig_zero]; norm_num⟩
    · exact ⟨1, by rw [h, hval, C8eig_one]⟩
    · exact ⟨2, by rw [h, hval, C8eig_two]; norm_num⟩
    · exact ⟨3, by rw [h, hval, C8eig_three]; norm_num⟩
    · exact ⟨4, by rw [h, hval, C8eig_four]; norm_num⟩

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

