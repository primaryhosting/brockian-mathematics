import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede every other command, including this
module docstring, so the header comment appears immediately after the single import.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₈`, over `ℂ`. -/

theorem huckel_C8_spectrum_explicit :
    spectrum ℂ ((cycleGraph 8).adjMatrix ℂ)
      = {2, ((Real.sqrt 2 : ℝ) : ℂ), 0, -((Real.sqrt 2 : ℝ) : ℂ), -2} := by
  rw [huckel_C8.2]
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have := cos_values k
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h | h | h <;> rw [h] <;> push_cast <;> simp
  · have h0 : ((2 * Real.cos (2 * Real.pi * ((0 : Fin 8) : ℕ) / 8) : ℝ) : ℂ) = 2 := by
      norm_num
    have h1 : ((2 * Real.cos (2 * Real.pi * ((1 : Fin 8) : ℕ) / 8) : ℝ) : ℂ)
        = ((Real.sqrt 2 : ℝ) : ℂ) := by
      rw [show (2 * Real.pi * ((1 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi / 4 by norm_num; ring,
        Real.cos_pi_div_four]
      push_cast; ring
    have h2 : ((2 * Real.cos (2 * Real.pi * ((2 : Fin 8) : ℕ) / 8) : ℝ) : ℂ) = 0 := by
      rw [show (2 * Real.pi * ((2 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi / 2 by norm_num; ring,
        Real.cos_pi_div_two]
      norm_num
    have h3 : ((2 * Real.cos (2 * Real.pi * ((3 : Fin 8) : ℕ) / 8) : ℝ) : ℂ)
        = -((Real.sqrt 2 : ℝ) : ℂ) := by
      rw [show (2 * Real.pi * ((3 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi - Real.pi / 4 by
        norm_num; ring, Real.cos_pi_sub, Real.cos_pi_div_four]
      push_cast; ring
    have h4 : ((2 * Real.cos (2 * Real.pi * ((4 : Fin 8) : ℕ) / 8) : ℝ) : ℂ) = -2 := by
      rw [show (2 * Real.pi * ((4 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi by norm_num; ring, Real.cos_pi]
      norm_num
    rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, h0.symm⟩
    · exact ⟨1, h1.symm⟩
    · exact ⟨2, h2.symm⟩
    · exact ⟨3, h3.symm⟩
    · exact ⟨4, h4.symm⟩

end Chem

