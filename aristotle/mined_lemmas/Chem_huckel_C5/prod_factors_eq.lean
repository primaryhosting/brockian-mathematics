import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header block
-- above appears immediately after the single `import Mathlib` line.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₅` written out explicitly. -/

lemma prod_factors_eq :
    (∏ k : Fin 5, (X - C (2 * Real.cos (2 * π * ((k : ℕ) : ℝ) / 5)))) =
      X ^ 5 - 5 * X ^ 3 + 5 * X - 2 := by
  have A0 : (2 : ℝ) * π * ((((0 : Fin 5)) : ℕ) : ℝ) / 5 = 0 := by norm_num
  have A1 : (2 : ℝ) * π * ((((1 : Fin 5)) : ℕ) : ℝ) / 5 = 2 * π / 5 := by norm_num
  have A2 : (2 : ℝ) * π * ((((2 : Fin 5)) : ℕ) : ℝ) / 5 = 4 * π / 5 := by norm_num; ring
  have A3 : (2 : ℝ) * π * ((((3 : Fin 5)) : ℕ) : ℝ) / 5 = 6 * π / 5 := by norm_num; ring
  have A4 : (2 : ℝ) * π * ((((4 : Fin 5)) : ℕ) : ℝ) / 5 = 8 * π / 5 := by norm_num; ring
  have B0 : (2 : ℝ) * 1 = 2 := by norm_num
  have B1 : (2 : ℝ) * ((√5 - 1) / 4) = (√5 - 1) / 2 := by ring
  have B2 : (2 : ℝ) * (-(1 + √5) / 4) = -(1 + √5) / 2 := by ring
  rw [Fin.prod_univ_five, A0, A1, A2, A3, A4, Real.cos_zero, cos_two_pi_div_five,
    cos_four_pi_div_five, cos_six_pi_div_five, cos_eight_pi_div_five, B0, B1, B2]
  rw [show (X - C 2) * (X - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2))
        * (X - C (-(1 + √5) / 2)) * (X - C ((√5 - 1) / 2))
      = (X - C 2) * ((X - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2)))
        * ((X - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2))) from by ring,
    quadratic_factor, C_ofNat]
  ring

/-- **Hückel theory for cyclic C₅.**  The characteristic polynomial of the adjacency matrix of
the cycle graph `C₅` splits as `∏ k, (X - 2 cos (2πk/5))`; equivalently, the adjacency
eigenvalues of `C₅`, counted with multiplicity, are `2 cos (2πk/5)` for `k = 0, …, 4`. -/
