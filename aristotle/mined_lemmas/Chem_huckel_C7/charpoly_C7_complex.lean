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

namespace Chem

open Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₇`, with vertices indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `±1` mod `7`. -/

private lemma charpoly_C7_complex :
    (C7.map (algebraMap ℝ ℂ)).charpoly =
      ∏ k : ZMod 7, (X - C ((algebraMap ℝ ℂ) (C7eigen k.val))) := by
  set D : Matrix (ZMod 7) (ZMod 7) ℂ :=
    Matrix.diagonal (fun k : ZMod 7 => (algebraMap ℝ ℂ) (C7eigen k.val)) with hD
  have hfac : C7.map (algebraMap ℝ ℂ) = F7 * (D * G7) := by
    rw [← mul_assoc, ← C7_mul_F7, mul_assoc, F7_mul_G7, mul_one]
  rw [hfac, Matrix.charpoly_mul_comm, mul_assoc, G7_mul_F7, mul_one, hD,
    Matrix.charpoly_diagonal]

