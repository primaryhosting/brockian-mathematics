/-
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

set_option autoImplicit false

namespace QPhys

open Polynomial

section Oscillator

variable (m ω hbar : ℝ)

/-- The Gaussian ground-state profile `exp (-m ω x² / (2ℏ))`. -/

lemma hamiltonian_stateFun (hm : m ≠ 0) (hw : ω ≠ 0) (hh : hbar ≠ 0) (p : Polynomial ℝ) :
    hamiltonian m ω hbar (stateFun m ω hbar p)
      = fun x => hbar * ω * stateFun m ω hbar (Mpoly m ω hbar p) x := by
  funext x
  unfold hamiltonian
  rw [deriv_stateFun, deriv_stateFun]
  simp only [stateFun, Dpoly, Mpoly, eval_sub, eval_add, eval_neg, eval_mul, eval_C, eval_X,
    derivative_sub, derivative_mul, derivative_C, derivative_X, zero_mul, one_mul, zero_add,
    add_zero, mul_zero]
  field_simp
  ring

end Oscillator
end QPhys

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

