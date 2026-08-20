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

theorem blochHamiltonian_mulVec_lowerSpinor (th ph : ℝ) :
    (blochHamiltonian th ph).mulVec (lowerSpinor th ph) = -lowerSpinor th ph := by
  have hs : Real.sin th = 2 * Real.sin (th / 2) * Real.cos (th / 2) := by
    have h := Real.sin_two_mul (th / 2)
    rw [show 2 * (th / 2) = th by ring] at h
    exact h
  have hc : Real.cos th = Real.cos (th / 2) ^ 2 - Real.sin (th / 2) ^ 2 := by
    have h := Real.cos_two_mul' (th / 2)
    rw [show 2 * (th / 2) = th by ring] at h
    exact h
  have hpyth : Real.sin (th / 2) ^ 2 + Real.cos (th / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have h1 : ((Real.sin (th / 2) : ℂ)) ^ 2 + ((Real.cos (th / 2) : ℂ)) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hpyth
  have hsC : ((Real.sin th : ℝ) : ℂ)
      = 2 * ((Real.sin (th / 2) : ℝ) : ℂ) * ((Real.cos (th / 2) : ℝ) : ℂ) := by
    rw [hs]; simp
  have hcC : ((Real.cos th : ℝ) : ℂ)
      = ((Real.cos (th / 2) : ℝ) : ℂ) ^ 2 - ((Real.sin (th / 2) : ℝ) : ℂ) ^ 2 := by
    rw [hc]; simp
  have hee : Complex.exp (Complex.I * (ph : ℂ)) * Complex.exp (-Complex.I * (ph : ℂ)) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  funext j
  fin_cases j <;>
    simp only [blochHamiltonian, lowerSpinor, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Pi.neg_apply, Fin.zero_eta, Fin.mk_one,
      Fin.isValue] <;>
    rw [hsC, hcC]
  · linear_combination (-(Real.sin (th / 2) : ℂ) * Complex.exp (-Complex.I * (ph : ℂ))) * h1
  · linear_combination (2 * (Real.sin (th / 2) : ℂ) ^ 2 * (Real.cos (th / 2) : ℂ)) * hee +
      (Real.cos (th / 2) : ℂ) * h1

/-! ## Berry connection and Berry curvature -/

/-- The `th`-component of the Berry connection `A_th = -i ⟨u | ∂_th u⟩` of the lower band. -/
