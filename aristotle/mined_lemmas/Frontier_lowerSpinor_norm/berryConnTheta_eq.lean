import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

namespace Frontier

noncomputable section

open Complex Real intervalIntegral

/-! ## The two-level Bloch Hamiltonian and its lower band -/

/-- The two-level Bloch Hamiltonian `H(th, ph) = d̂(th,ph) · σ⃗`, where
`d̂ = (sin th cos ph, sin th sin ph, cos th)` is a unit vector and `σ⃗` are the Pauli matrices.
Explicitly `H = [[cos th, sin th e^{-iph}], [sin th e^{iph}, -cos th]]`. -/

theorem berryConnTheta_eq (th ph : ℝ) : berryConnTheta th ph = 0 := by
  have hsin := hasDerivAt_sin_half th
  have hcos := hasDerivAt_cos_half th
  have hd0 : deriv (fun t : ℝ => lowerSpinor t ph 0) th
      = ((Real.cos (th / 2) * (1 / 2) : ℝ) : ℂ) * Complex.exp (-Complex.I * (ph : ℂ)) := by
    simpa [lowerSpinor] using
      (hsin.ofReal_comp.mul_const (Complex.exp (-Complex.I * (ph : ℂ)))).deriv
  have hd1 : deriv (fun t : ℝ => lowerSpinor t ph 1) th
      = -((-Real.sin (th / 2) * (1 / 2) : ℝ) : ℂ) := by
    simpa [lowerSpinor] using hcos.ofReal_comp.neg.deriv
  have v0 : lowerSpinor th ph 0 = (Real.sin (th / 2) : ℂ) * Complex.exp (-Complex.I * (ph : ℂ)) :=
    rfl
  have v1 : lowerSpinor th ph 1 = -(Real.cos (th / 2) : ℂ) := rfl
  have key : (-Complex.I * ∑ j : Fin 2,
      (starRingEnd ℂ) (lowerSpinor th ph j) * deriv (fun t : ℝ => lowerSpinor t ph j) th)
      = ((0 : ℝ) : ℂ) := by
    rw [Fin.sum_univ_two, hd0, hd1, v0, v1]
    simp only [map_mul, map_neg, Complex.conj_ofReal, conj_exp_neg, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Complex.ofReal_zero]
    linear_combination
      (-Complex.I * (Real.sin (th / 2) : ℂ) * (Real.cos (th / 2) : ℂ) / 2) * exp_mul_exp_neg ph
  rw [berryConnTheta, key, Complex.ofReal_re]

/-- The `ph`-component of the Berry connection equals `-sin²(th/2)`. -/
