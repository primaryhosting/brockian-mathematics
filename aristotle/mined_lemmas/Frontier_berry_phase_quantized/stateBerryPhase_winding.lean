/-
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

open Set MeasureTheory

namespace Frontier

/-- The **Berry connection** is modelled as a real one-form on a two-dimensional parameter
space, i.e. a map `A : ℝ × ℝ → ℝ × ℝ` whose value `A p = (A₁ p, A₂ p)` gives the components
of the form `A₁ dx + A₂ dy` at the parameter point `p`. -/
abbrev BerryConnection := ℝ × ℝ → ℝ × ℝ

/-- The **Berry curvature** of a Berry connection `A` at a parameter point `p`:
`F = ∂₁ A₂ - ∂₂ A₁`, the exterior derivative of the connection one-form. -/

theorem stateBerryPhase_winding (n : ℤ) :
    stateBerryPhase (fun t => Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I)) (2 * Real.pi)
      = -(2 * Real.pi * n) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I))
      (Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I) * ((n : ℂ) * Complex.I)) t := by
    intro t
    have h0 : HasDerivAt (fun t : ℝ => ((n : ℂ) * (t : ℂ) * Complex.I))
        ((n : ℂ) * Complex.I) t := by
      have hre : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 t := Complex.ofRealCLM.hasDerivAt
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((hre.const_mul ((n : ℂ))).mul_const Complex.I)
    simpa using h0.cexp
  have hint : ∀ t : ℝ,
      (starRingEnd ℂ) (Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I)) *
        deriv (fun t : ℝ => Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I)) t
        = (n : ℂ) * Complex.I := by
    intro t
    rw [(hd t).deriv, ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
    have hz : (starRingEnd ℂ) ((n : ℂ) * (t : ℂ) * Complex.I) +
        (n : ℂ) * (t : ℂ) * Complex.I = 0 := by
      simp
    rw [hz]
    simp
  rw [stateBerryPhase]
  simp only [hint]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination (2 * (Real.pi : ℂ) * (n : ℂ)) * Complex.I_mul_I

/-- The Berry phase of the winding family `ψₙ(t) = exp(i n t)` is a real integer multiple
of `2π`. -/
