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

/-
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Complex
open scoped Convolution

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Test functions and the minimal Schrödinger expression -/

/-- A test function on the line: smooth with compact support. -/

private theorem sol_formula {c lam : ℂ} (hlam : lam ^ 2 = c) {y : ℝ → ℂ} (hy : ContDiff ℝ 2 y)
    (hode : ∀ t, deriv (deriv y) t = c * y t) :
    ∀ t : ℝ, deriv y t + lam * y t = (deriv y 0 + lam * y 0) * Complex.exp (lam * t) := by
  have hdy : Differentiable ℝ y := hy.differentiable (by norm_num)
  have hdy' : Differentiable ℝ (deriv y) := ContDiff.differentiable_deriv_two hy
  set w : ℝ → ℂ := fun t => deriv y t + lam * y t with hw
  have hwd : ∀ t : ℝ, HasDerivAt w (lam * w t) t := by
    intro t
    have h1 : HasDerivAt (deriv y) (deriv (deriv y) t) t := (hdy' t).hasDerivAt
    have h2 : HasDerivAt y (deriv y t) t := (hdy t).hasDerivAt
    have h3 := h1.add (h2.const_mul lam)
    rw [hode t] at h3
    convert h3 using 1
    rw [hw]
    ring_nf
    rw [← hlam]; ring
  have hgd : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => w t * Complex.exp (-(lam * t))) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(lam * t)))
        (-lam * Complex.exp (-(lam * t))) t := by
      have h0 : HasDerivAt (fun t : ℝ => -(lam * (t : ℂ))) (-lam) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul lam).neg
      simpa [mul_comm] using h0.cexp
    have h2 := (hwd t).mul h1
    convert h2 using 1
    ring
  intro t
  have h0 : w t * Complex.exp (-(lam * t)) = w 0 * Complex.exp (-(lam * (0 : ℝ))) :=
    is_const_of_deriv_eq_zero (fun x => (hgd x).differentiableAt) (fun x => (hgd x).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one] at h0
  have key : w t = w t * Complex.exp (-(lam * t)) * Complex.exp (lam * t) := by
    rw [mul_assoc, ← Complex.exp_add]; simp
  rw [h0] at key
  simpa [hw] using key

/-- **ODE input.** A bounded classical solution of `y'' = c y` with `c` non-real vanishes.
This is the limit-point mechanism: for non-real spectral parameter both exponential
solutions blow up at one of the two ends of the line. -/
