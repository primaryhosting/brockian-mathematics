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

open Polynomial Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₇` (the Hückel matrix of cycloheptatrienyl,
with `α = 0`, `β = 1`), as a real `7 × 7` matrix. -/

lemma dd_eq (k : Fin 7) :
    dd k = ((2 * Real.cos (2 * Real.pi * k.val / 7) : ℝ) : ℂ) := by
  have h1 : ee k = Complex.exp (((2 * Real.pi * k.val / 7 : ℝ) : ℂ) * Complex.I) := by
    rw [ee, om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [dd, ee_neg, h1, ← Complex.exp_neg, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- The (unnormalized) discrete Fourier matrix. -/
