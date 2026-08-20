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

lemma quadratic_factor :
    (X - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2)) = (X ^ 2 + X - 1 : ℝ[X]) := by
  have hs : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have e1 : ((√5 - 1) / 2) + (-(1 + √5) / 2) = -1 := by ring
  have e2 : ((√5 - 1) / 2) * (-(1 + √5) / 2) = -1 := by nlinarith [hs]
  have key : (X - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2))
      = X ^ 2 - C (((√5 - 1) / 2) + (-(1 + √5) / 2)) * X
          + C (((√5 - 1) / 2) * (-(1 + √5) / 2)) := by
    rw [C_add, C_mul]; ring
  rw [key, e1, e2]
  simp
  ring

/-- The product of the linear factors `X - 2 cos (2πk/5)` over `k = 0, …, 4`. -/
