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
lemma hasDerivAt_expDecay (a c t : ℝ) :
    HasDerivAt (fun t : ℝ => c * Real.exp (-(a * t))) (-a * (c * Real.exp (-(a * t)))) t := by
  have h : HasDerivAt (fun t : ℝ => -(a * t)) (-a) t := by
    simpa using ((hasDerivAt_id t).const_mul a).neg
  have h2 := (h.exp).const_mul c
  convert h2 using 1
  ring

/-- Uniqueness for the linear relaxation equation `f' = -a f`: a solution is determined
by its value at time `0`, and is the exponential decay `t ↦ f 0 * e^{-a t}`. -/
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
noncomputable def relaxRate : ℝ := S.k / S.gamma

lemma relaxRate_pos : 0 < S.relaxRate := div_pos S.k_pos S.gamma_pos

/-- The equilibrium autocorrelation function `C t = ⟪x(0) x(t)⟫`.  In equilibrium the
position decays deterministically, `⟪x(0) x(t)⟫ = ⟪x(0)²⟫ e^{-(k/gamma) t}`, and
equipartition fixes the variance `⟪x²⟫ = 1 / (beta k)`. -/
noncomputable def corr (t : ℝ) : ℝ := (1 / (S.beta * S.k)) * Real.exp (-(S.relaxRate * t))

/-- The linear response (after-effect) function: the mean displacement at time `t`
produced by a unit impulse of force at time `0`.  The impulse produces an instantaneous
displacement `1 / gamma`, which then relaxes at rate `k / gamma`. -/
noncomputable def response (t : ℝ) : ℝ := (1 / S.gamma) * Real.exp (-(S.relaxRate * t))

@[simp] lemma corr_zero : S.corr 0 = 1 / (S.beta * S.k) := by
  simp [corr]

@[simp] lemma response_zero : S.response 0 = 1 / S.gamma := by
  simp [response]

/-- Equipartition of energy: the mean potential energy is `k_B T / 2`. -/
lemma equipartition : (1 / 2) * S.k * S.corr 0 = 1 / (2 * S.beta) := by
  have hk := S.k_pos.ne'
  have hb := S.beta_pos.ne'
  rw [corr_zero]
  field_simp

/-- The correlation function solves the deterministic relaxation equation
`gamma * C' = -k * C`. -/
lemma hasDerivAt_corr (t : ℝ) :
    HasDerivAt S.corr (-(S.relaxRate) * S.corr t) t :=
  hasDerivAt_expDecay S.relaxRate (1 / (S.beta * S.k)) t

/-- The response function solves the same relaxation equation `gamma * R' = -k * R`. -/
lemma hasDerivAt_response (t : ℝ) :
    HasDerivAt S.response (-(S.relaxRate) * S.response t) t :=
  hasDerivAt_expDecay S.relaxRate (1 / S.gamma) t

lemma deriv_corr (t : ℝ) : deriv S.corr t = -(S.relaxRate) * S.corr t :=
  (S.hasDerivAt_corr t).deriv

lemma deriv_response (t : ℝ) : deriv S.response t = -(S.relaxRate) * S.response t :=
  (S.hasDerivAt_response t).deriv

/-- The response function is the unique solution of the relaxation equation
`gamma * f' = -k * f` with the impulse initial condition `f 0 = 1 / gamma`. -/
lemma eq_response_of_ode {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, HasDerivAt f (-(S.relaxRate) * f t) t) (h0 : f 0 = 1 / S.gamma) :
    f = S.response := by
  have h := eq_expDecay_of_ode S.relaxRate hf
  rw [h0] at h
  exact h

/-- Onsager's regression hypothesis plus equipartition determine the equilibrium
autocorrelation function: any solution of the macroscopic relaxation equation
`gamma * f' = -k * f` whose initial value is the equipartition variance
`⟪x²⟫ = 1 / (beta k)` is the correlation function `C`. -/
lemma eq_corr_of_ode {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, HasDerivAt f (-(S.relaxRate) * f t) t) (h0 : f 0 = 1 / (S.beta * S.k)) :
    f = S.corr := by
  have h := eq_expDecay_of_ode S.relaxRate hf
  rw [h0] at h
  exact h

end LangevinSystem

open LangevinSystem

/-- **Fluctuation–dissipation theorem** (classical, time domain).

For a system in thermal equilibrium at inverse temperature `beta`, the linear response
function `R` — the after-effect of an impulsive external force — is determined by the
spontaneous equilibrium fluctuations through

`R t = - beta * (d/dt) C t`,

where `C t = ⟪x(0) x(t)⟫` is the equilibrium autocorrelation function.  Dissipation
(the left-hand side) is thus rigidly tied to fluctuations (the right-hand side). -/
theorem fluctuation_dissipation (S : LangevinSystem) (t : ℝ) :
    S.response t = -S.beta * deriv S.corr t := by
  have hk := S.k_pos.ne'
  have hb := S.beta_pos.ne'
  have hg := S.gamma_pos.ne'
  rw [S.deriv_corr]
  simp only [corr, response, LangevinSystem.relaxRate]
  field_simp

/-- Static (zero-frequency) form of the fluctuation–dissipation theorem: the static
susceptibility, i.e. the total integrated response to a steady unit force, equals
`beta` times the equilibrium variance. -/
theorem fluctuation_dissipation_static (S : LangevinSystem) :
    (∫ t in Set.Ioi (0 : ℝ), S.response t) = S.beta * S.corr 0 := by
  have hrate := S.relaxRate_pos
  have hint : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(S.relaxRate * t)))
      = 1 / S.relaxRate := by
    have := integral_exp_mul_Ioi (a := -S.relaxRate) (by linarith) 0
    simp only [neg_mul, mul_zero, Real.exp_zero] at this
    rw [this]
    field_simp
  have hk := S.k_pos.ne'
  have hb := S.beta_pos.ne'
  have hg := S.gamma_pos.ne'
  simp only [response, corr_zero]
  rw [MeasureTheory.integral_const_mul, hint]
  simp only [LangevinSystem.relaxRate]
  field_simp

end Phys

