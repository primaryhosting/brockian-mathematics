import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix SimpleGraph

/-- The angle `2π/n` for the cycle `C_n` with `n = m + 3`. -/

lemma det_fourierMat_ne_zero : (fourierMat m).det ≠ 0 := by
  have hv : fourierMat m = (Matrix.vandermonde (fun k : Fin (m + 3) => cycRoot m ^ k.val))ᵀ := by
    ext j k
    simp [fourierMat, Matrix.vandermonde, Matrix.transpose_apply, ← pow_mul, mul_comm]
  rw [hv, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr
    (fun a b h => Fin.ext (cycRoot_isPrimitiveRoot.pow_inj a.isLt b.isLt h))

