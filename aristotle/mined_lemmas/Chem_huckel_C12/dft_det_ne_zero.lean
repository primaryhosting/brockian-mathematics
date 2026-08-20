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
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators Real
open Polynomial Matrix

namespace Chem

/-- A primitive 12-th root of unity. -/

lemma dft_det_ne_zero : dftC12.det ≠ 0 := by
  rw [dft_eq_vandermonde, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_))
  have hij : i < j := Finset.mem_Ioi.mp hj
  refine sub_ne_zero.mpr (fun h => ?_)
  have := isPrimitiveRoot_om.pow_inj j.isLt i.isLt h
  omega

/-- **Hückel theory for `C₁₂`**: the characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₂` factors as `∏ₖ (X - 2 cos (2πk/12))`, i.e. the adjacency eigenvalues of `C₁₂`
are exactly `2 cos (2πk/12)` for `k = 0, …, 11`, counted with multiplicity. -/
