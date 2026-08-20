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

theorem berryConnPhi_eq (th ph : ℝ) : berryConnPhi th ph = -(Real.sin (th / 2)) ^ 2 := by
  have hlin : HasDerivAt (fun s : ℝ => -Complex.I * (s : ℂ)) (-Complex.I) ph := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := ph)).const_mul (-Complex.I)
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-Complex.I * (s : ℂ)))
      (Complex.exp (-Complex.I * (ph : ℂ)) * -Complex.I) ph := hlin.cexp
  have hd0 : deriv (fun s : ℝ => lowerSpinor th s 0) ph
      = (Real.sin (th / 2) : ℂ) * (Complex.exp (-Complex.I * (ph : ℂ)) * -Complex.I) := by
    simpa [lowerSpinor] using (hexp.const_mul ((Real.sin (th / 2) : ℝ) : ℂ)).deriv
  have hd1 : deriv (fun s : ℝ => lowerSpinor th s 1) ph = 0 := by simp [lowerSpinor]
  have v0 : lowerSpinor th ph 0 = (Real.sin (th / 2) : ℂ) * Complex.exp (-Complex.I * (ph : ℂ)) :=
    rfl
  have v1 : lowerSpinor th ph 1 = -(Real.cos (th / 2) : ℂ) := rfl
  have key : (-Complex.I * ∑ j : Fin 2,
      (starRingEnd ℂ) (lowerSpinor th ph j) * deriv (fun s : ℝ => lowerSpinor th s j) ph)
      = ((-(Real.sin (th / 2)) ^ 2 : ℝ) : ℂ) := by
    rw [Fin.sum_univ_two, hd0, hd1, v0, v1, map_mul, Complex.conj_ofReal, conj_exp_neg,
      Complex.ofReal_neg, Complex.ofReal_pow]
    linear_combination (Complex.I ^ 2 * (Real.sin (th / 2) : ℂ) ^ 2) * exp_mul_exp_neg ph +
      ((Real.sin (th / 2) : ℂ) ^ 2) * Complex.I_sq
  rw [berryConnPhi, key, Complex.ofReal_re]

/-- The Berry curvature of the lower band is `-(1/2) sin th`: a magnetic monopole of unit
charge sitting at the degeneracy point. -/
