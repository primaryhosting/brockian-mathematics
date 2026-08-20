import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₅`, i.e. the Hückel matrix of
cyclopentadienyl (with `α = 0`, `β = 1`). -/

lemma mem_spectrum_iff (t : ℝ) :
    t ∈ spectrum ℝ C5 ↔ t = 2 ∨ t = (Real.sqrt 5 - 1)/2 ∨ t = -(1 + Real.sqrt 5)/2 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, charpoly_eval,
    quintic_root_iff]

