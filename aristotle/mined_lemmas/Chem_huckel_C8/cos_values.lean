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

lemma cos_values (k : Fin 8) :
    2 * Real.cos (2 * Real.pi * (k : ℕ) / 8)
      ∈ ({2, Real.sqrt 2, 0, -Real.sqrt 2, -2} : Set ℝ) := by
  have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  fin_cases k <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  · left
    rw [show (2 * Real.pi * ((0 : ℕ) : ℝ) / 8 : ℝ) = 0 by norm_num, Real.cos_zero]; norm_num
  · right; left
    rw [show (2 * Real.pi * ((1 : ℕ) : ℝ) / 8 : ℝ) = Real.pi / 4 by norm_num; ring, h4]; ring
  · right; right; left
    rw [show (2 * Real.pi * ((2 : ℕ) : ℝ) / 8 : ℝ) = Real.pi / 2 by norm_num; ring,
      Real.cos_pi_div_two]; ring
  · right; right; right; left
    rw [show (2 * Real.pi * ((3 : ℕ) : ℝ) / 8 : ℝ) = Real.pi - Real.pi / 4 by norm_num; ring,
      Real.cos_pi_sub, h4]; ring
  · right; right; right; right
    rw [show (2 * Real.pi * ((4 : ℕ) : ℝ) / 8 : ℝ) = Real.pi by norm_num; ring, Real.cos_pi]
    norm_num
  · right; right; right; left
    rw [show (2 * Real.pi * ((5 : ℕ) : ℝ) / 8 : ℝ) = Real.pi - (-(Real.pi / 4)) by
      norm_num; ring, Real.cos_pi_sub, Real.cos_neg, h4]; ring
  · right; right; left
    rw [show (2 * Real.pi * ((6 : ℕ) : ℝ) / 8 : ℝ) = Real.pi - (-(Real.pi / 2)) by
      norm_num; ring, Real.cos_pi_sub, Real.cos_neg, Real.cos_pi_div_two]; ring
  · right; left
    rw [show (2 * Real.pi * ((7 : ℕ) : ℝ) / 8 : ℝ) = 2 * Real.pi - Real.pi / 4 by
      norm_num; ring, Real.cos_two_pi_sub, h4]; ring

/-- Consequence of `huckel_C8`: the spectrum of the adjacency matrix of `C₈` is exactly
`{2, √2, 0, -√2, -2}` (the Hückel π-orbital energies of cyclooctatetraene in units of β,
relative to α). -/
