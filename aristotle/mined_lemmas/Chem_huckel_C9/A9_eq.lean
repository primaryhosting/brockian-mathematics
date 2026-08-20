import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
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

set_option grind.warning false

namespace Chem

open Complex Matrix Polynomial

/-- A primitive ninth root of unity. -/

theorem A9_eq : A9 = F9 * Matrix.diagonal lam * G9 := by
  have h : A9 * F9 * G9 = F9 * Matrix.diagonal lam * G9 := by rw [A9_mul_F9]
  rwa [Matrix.mul_assoc, F9_mul_G9, Matrix.mul_one] at h

/-- The characteristic polynomial of the adjacency matrix of the cycle graph `C₉`
factors as `∏ k, (X - 2 cos (2πk/9))`. -/
