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
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Finset

/-!
Mathlib (as of this version) contains no quantum-Fourier-transform matrix, so the matrix is
defined here.  The unitarity proof rests on the Mathlib lemmas
`Complex.isPrimitiveRoot_exp` (that `exp (2πI/N)` is a primitive `N`-th root of unity),
`geom_sum_eq` (closed form of a geometric sum) and `Matrix.mem_unitaryGroup_iff'`.
-/

namespace QC

/-- The `N × N` discrete Fourier transform (QFT) matrix:
`F i j = exp(2πi·jk/N) / √N`. -/

lemma sum_pow_eq_zero_of_ne_one {N : ℕ} {w : ℂ} (hw : w ^ N = 1) (hne : w ≠ 1) :
    ∑ j : Fin N, w ^ (j : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => w ^ j) N, geom_sum_eq hne, hw, sub_self, zero_div]

/-- Entries of the QFT matrix as powers of the primitive root `exp(2πI/N)`. -/
