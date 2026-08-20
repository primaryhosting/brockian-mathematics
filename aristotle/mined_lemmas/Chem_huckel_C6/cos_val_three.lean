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

/-
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Chem

/-- Adjacency matrix of the cycle graph `C₆` (the Hückel connectivity matrix of benzene):
vertex `i` is adjacent to `i ± 1 mod 6`. -/

lemma cos_val_three : 2 * Complex.cos (2 * (Real.pi : ℂ) * ((3 : ℕ) : ℂ) / 6) = -2 := by
  rw [two_mul_cos_ofNat, show (2 * Real.pi * ((3 : ℕ) : ℝ) / 6 : ℝ) = Real.pi by push_cast; ring,
    Real.cos_pi]
  norm_num

