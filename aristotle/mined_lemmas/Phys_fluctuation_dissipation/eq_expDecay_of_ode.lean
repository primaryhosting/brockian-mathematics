import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
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

namespace Phys

/-- Derivative of an exponentially decaying observable `t ↦ c e^{-a t}`. -/

lemma eq_expDecay_of_ode (a : ℝ) {f : ℝ → ℝ} (hf : ∀ t : ℝ, HasDerivAt f (-a * f t) t) :
    f = fun t : ℝ => f 0 * Real.exp (-(a * t)) := by
  have hgd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f t * Real.exp (a * t)) 0 t := by
    intro t
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (a * t)) (a * Real.exp (a * t)) t := by
      have h : HasDerivAt (fun t : ℝ => a * t) a t := by
        simpa using (hasDerivAt_id t).const_mul a
      simpa [mul_comm] using h.exp
    have h2 := (hf t).mul hexp
    convert h2 using 1
    ring
  have hdiff : Differentiable ℝ (fun t : ℝ => f t * Real.exp (a * t)) :=
    fun t => (hgd t).differentiableAt
  funext t
  have ht : f t * Real.exp (a * t) = f 0 * Real.exp (a * 0) :=
    is_const_of_deriv_eq_zero hdiff (fun x => (hgd x).deriv) t 0
  have hne : Real.exp (a * t) ≠ 0 := (Real.exp_pos _).ne'
  have h1 : f t = (f 0) / Real.exp (a * t) := by
    refine eq_div_of_mul_eq hne ?_
    simpa using ht
  simpa [Real.exp_neg, div_eq_mul_inv] using h1

/-- Data of an overdamped Langevin (Ornstein–Uhlenbeck) system in thermal equilibrium:
a harmonic potential of stiffness `k`, friction coefficient `gamma`, at inverse
temperature `beta = 1 / (k_B T)`.  The dynamics is `gamma * x' = -k * x + noise`. -/
structure LangevinSystem where
  /-- Friction coefficient. -/
  gamma : ℝ
  /-- Stiffness of the harmonic potential. -/
  k : ℝ
  /-- Inverse temperature `1 / (k_B T)`. -/
  beta : ℝ
  gamma_pos : 0 < gamma
  k_pos : 0 < k
  beta_pos : 0 < beta

namespace LangevinSystem

variable (S : LangevinSystem)

/-- The relaxation rate `k / gamma` of the overdamped dynamics. -/
