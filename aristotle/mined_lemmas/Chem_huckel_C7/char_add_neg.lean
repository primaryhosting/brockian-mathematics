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

private lemma char_add_neg (n : ℕ) :
    ZMod.stdAddChar ((n : ZMod 7)) + ZMod.stdAddChar (-(n : ZMod 7)) = ((C7eigen n : ℝ) : ℂ) := by
  have h1 : ((n : ZMod 7)) = ((n : ℤ) : ZMod 7) := by push_cast; ring
  rw [C7eigen, h1, ← Int.cast_neg, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  rw [Complex.ofReal_mul, Complex.ofReal_cos]
  push_cast
  rw [Complex.two_cos]
  ring_nf

