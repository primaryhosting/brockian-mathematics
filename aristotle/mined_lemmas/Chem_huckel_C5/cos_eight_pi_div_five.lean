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

lemma cos_eight_pi_div_five : Real.cos (8 * π / 5) = (√5 - 1) / 4 := by
  have h : (8 : ℝ) * π / 5 = 2 * π - 2 * (π / 5) := by ring
  rw [h, Real.cos_two_pi_sub, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- The two nontrivial Hückel eigenvalues of `C₅` are the roots of `X² + X - 1`. -/
