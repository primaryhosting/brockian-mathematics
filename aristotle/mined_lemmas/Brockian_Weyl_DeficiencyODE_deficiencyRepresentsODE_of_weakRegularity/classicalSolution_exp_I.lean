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

import Brockian.Weyl.WeakDerivative

/-!
# Weyl deficiency spaces are represented by solutions of the Schrödinger ODE

For a continuous potential `q : ℝ → ℝ` and a spectral parameter `z : ℂ`, consider the
formally symmetric differential expression `τ u = -u'' + q u` on the line.  The minimal
operator is the restriction of `τ` to test functions, and the deficiency space at `z`
consists of the `L²` functions `u` which satisfy `τ u = z u` *weakly*, i.e. in the sense
of distributions:

  `∫ u φ'' = ∫ (q - z) u φ`   for all real test functions `φ`.

The main result of this file, `deficiencyRepresentsODE_of_weakRegularity`, states that
this deficiency space coincides with the set of `L²` functions which agree almost
everywhere with a *classical* (twice differentiable) solution of the ODE
`-u'' + q u = z u`.

The nontrivial inclusion is a regularity statement — every weak solution is almost
everywhere a classical solution — which is proved here from scratch (`weakRegularity`)
from the du Bois-Reymond lemmas of `Brockian.Weyl.WeakDerivative`; consequently the final

theorem classicalSolution_exp_I :
    ClassicalSolution (fun _ => 0) 1 (fun x : ℝ => Complex.exp (Complex.I * x)) := by
  refine ⟨fun x => Complex.I * Complex.exp (Complex.I * x), fun x => ?_, fun x => ?_⟩
  · have h := (((hasDerivAt_id x).ofReal_comp).const_mul Complex.I).cexp
    simpa [mul_comm] using h
  · have h := ((((hasDerivAt_id x).ofReal_comp).const_mul Complex.I).cexp).const_mul Complex.I
    simp only [id, Complex.ofReal_one, mul_one] at h
    convert h using 1
    simp only [Complex.ofReal_zero, zero_sub]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The corresponding weak solution, obtained from `WeakSolution.of_classical`. -/
