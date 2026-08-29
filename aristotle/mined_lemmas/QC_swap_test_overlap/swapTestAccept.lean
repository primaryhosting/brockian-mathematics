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
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open scoped ComplexConjugate

/-- The tensor (Kronecker) product of two `n`-dimensional pure states, viewed as a vector
indexed by pairs: `(x ⊗ y) (i, j) = x i * y j`. -/

noncomputable def swapTestAccept {n : ℕ} (x y : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ‖(1 / 2 : ℂ) • (kron x y + kron y x)‖ ^ 2

/-- **Swap test overlap.** For unit vectors (pure states) `x` and `y`, the SWAP test accepts
with probability `(1 + |⟪x, y⟫|²) / 2`. -/
