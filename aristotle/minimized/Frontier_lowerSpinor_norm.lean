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

def lowerSpinor (th ph : ℝ) : Fin 2 → ℂ :=
  ![(Real.sin (th / 2) : ℂ) * Complex.exp (-Complex.I * ph), -(Real.cos (th / 2) : ℂ)]

/-- The lower spinor is normalized. -/

theorem lowerSpinor_norm (th ph : ℝ) :
    ∑ j : Fin 2, ‖lowerSpinor th ph j‖ ^ 2 = 1 := by
  have hexp : ‖Complex.exp (-Complex.I * (ph : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  simp only [lowerSpinor, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    norm_mul, hexp, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_one]
  rw [sq_abs, sq_abs]
  exact Real.sin_sq_add_cos_sq _

/-- The lower spinor is an eigenvector of the Bloch Hamiltonian with eigenvalue `-1`. -/
