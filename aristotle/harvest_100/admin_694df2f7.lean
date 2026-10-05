/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
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

set_option pp.fullNames false

namespace Phys

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Kato's geometric generator `K(s) = [P'(s), P(s)] = P'(s)P(s) - P(s)P'(s)` associated with a
differentiable family of spectral projections `P` with derivative `dP`. -/
noncomputable def katoGenerator (P dP : ℝ → (E →L[ℂ] E)) (s : ℝ) : E →L[ℂ] E :=
  dP s * P s - P s * dP s

/-- The generator of the adiabatic evolution at slowness parameter `τ`:
`G(s) = -i τ H(s) + K(s)`, the dynamical part plus Kato's geometric part. -/
noncomputable def adiabaticGenerator (τ : ℝ) (H P dP : ℝ → (E →L[ℂ] E)) (s : ℝ) : E →L[ℂ] E :=
  (-(Complex.I * (τ : ℂ))) • H s + katoGenerator P dP s

/-- Uniqueness for the linear ODE `X' = G X` in a Banach algebra: a solution vanishing at `0`
vanishes identically.  (Proved by Grönwall's inequality, forwards and backwards in time.) -/
theorem linear_ode_eq_zero {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {G X : ℝ → 𝔸}
    (hGc : Continuous G) (hX : ∀ t, HasDerivAt X (G t * X t) t) (hX0 : X 0 = 0) :
    ∀ s, X s = 0 := by
  have hXc : Continuous X := continuous_iff_continuousAt.2 fun t => (hX t).continuousAt
  have key : ∀ b : ℝ, 0 ≤ b → ∀ s ∈ Icc (0 : ℝ) b, X s = 0 := by
    intro b hb
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn
      hGc.continuousOn
    refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := C)
      hXc.continuousOn (fun t _ => ((hX t).hasDerivWithinAt)) hX0 ?_
    intro t ht
    calc ‖G t * X t‖ ≤ ‖G t‖ * ‖X t‖ := norm_mul_le _ _
      _ ≤ C * ‖X t‖ := by
          exact mul_le_mul_of_nonneg_right (hC t (Ico_subset_Icc_self ht)) (norm_nonneg _)
  have keyneg : ∀ b : ℝ, 0 ≤ b → ∀ s ∈ Icc (0 : ℝ) b, X (-s) = 0 := by
    intro b hb
    set Y : ℝ → 𝔸 := fun u => X (-u) with hY
    have hYd : ∀ u : ℝ, HasDerivAt Y (-(G (-u)) * X (-u)) u := by
      intro u
      have := HasDerivAt.scomp (𝕜 := ℝ) (𝕜' := ℝ) u (hX (-u)) (hasDerivAt_neg u)
      simpa [hY, Function.comp, neg_mul] using this
    have hYc : Continuous Y := hXc.comp continuous_neg
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn
      (Continuous.continuousOn (by fun_prop : Continuous fun u : ℝ => -(G (-u))))
    have : ∀ s ∈ Icc (0 : ℝ) b, Y s = 0 := by
      refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := C)
        hYc.continuousOn (fun t _ => (hYd t).hasDerivWithinAt) (by simpa [hY] using hX0) ?_
      intro t ht
      calc ‖-(G (-t)) * X (-t)‖ ≤ ‖-(G (-t))‖ * ‖X (-t)‖ := norm_mul_le _ _
        _ ≤ C * ‖Y t‖ := by
            exact mul_le_mul_of_nonneg_right (hC t (Ico_subset_Icc_self ht)) (norm_nonneg _)
    exact this
  intro s
  rcases le_total 0 s with h | h
  · exact key s h s ⟨h, le_rfl⟩
  · have : (0 : ℝ) ≤ -s := by linarith
    simpa using keyneg (-s) this (-s) ⟨this, le_rfl⟩

section Setup

variable {H P dP U : ℝ → (E →L[ℂ] E)} {ev : ℝ → ℂ} {τ : ℝ}

/-- Differentiating `P(s)² = P(s)` gives `P' = P'P + PP'`. -/
theorem deriv_proj_eq (hPP : ∀ s, P s * P s = P s) (hdP : ∀ s, HasDerivAt P (dP s) s) (s : ℝ) :
    dP s = dP s * P s + P s * dP s := by
  have h1 : HasDerivAt (fun t => P t * P t) (dP s * P s + P s * dP s) s := (hdP s).mul (hdP s)
  have h2 : HasDerivAt (fun t => P t * P t) (dP s) s := by
    have : (fun t => P t * P t) = P := funext hPP
    rw [this]; exact hdP s
  exact h2.unique h1

/-- The "sandwich" identity `P P' P = 0` for a differentiable family of projections. -/
theorem proj_sandwich_eq_zero (hPP : ∀ s, P s * P s = P s) (hdP : ∀ s, HasDerivAt P (dP s) s)
    (s : ℝ) : P s * dP s * P s = 0 := by
  have hd := deriv_proj_eq hPP hdP s
  have hsq := hPP s
  have e : P s * dP s * P s = P s * dP s * P s + P s * dP s * P s := by
    calc P s * dP s * P s = P s * (dP s * P s + P s * dP s) * P s := by rw [← hd]
      _ = P s * dP s * (P s * P s) + (P s * P s) * dP s * P s := by noncomm_ring
      _ = P s * dP s * P s + P s * dP s * P s := by rw [hsq]
  simpa using sub_eq_zero_of_eq e

/-- The key algebraic intertwining identity: `P' + P G = G P`, where `G` is the adiabatic
generator.  This is what makes the adiabatic evolution preserve the instantaneous eigenspaces. -/
theorem adiabaticGenerator_intertwine (hPP : ∀ s, P s * P s = P s)
    (hdP : ∀ s, HasDerivAt P (dP s) s)
    (hHP : ∀ s, H s * P s = ev s • P s) (hPH : ∀ s, P s * H s = ev s • P s) (s : ℝ) :
    dP s + P s * adiabaticGenerator τ H P dP s
      = adiabaticGenerator τ H P dP s * P s := by
  have hd := deriv_proj_eq hPP hdP s
  have hsand := proj_sandwich_eq_zero hPP hdP s
  have hsq := hPP s
  have hsq2 : dP s * P s * P s = dP s * P s := by rw [mul_assoc, hsq]
  simp only [adiabaticGenerator, katoGenerator, mul_add, mul_sub, add_mul, sub_mul,
    mul_smul_comm, smul_mul_assoc, ← mul_assoc, hPH, hHP, hsq, hsq2, hsand]
  set a := dP s * P s with ha
  set b := P s * dP s with hb
  rw [hd]
  abel

variable (H P dP U ev τ) in
/-- The intertwining relation `P(s) U(s) = U(s) P(0)` for the adiabatic evolution `U`:
the adiabatic propagator maps the initial spectral subspace onto the instantaneous one. -/
theorem adiabatic_intertwining
    (hPP : ∀ s, P s * P s = P s) (hdP : ∀ s, HasDerivAt P (dP s) s) (hdPc : Continuous dP)
    (hHc : Continuous H)
    (hHP : ∀ s, H s * P s = ev s • P s) (hPH : ∀ s, P s * H s = ev s • P s)
    (hU0 : U 0 = 1)
    (hU : ∀ s, HasDerivAt U (adiabaticGenerator τ H P dP s * U s) s) (s : ℝ) :
    P s * U s = U s * P 0 := by
  set G : ℝ → (E →L[ℂ] E) := adiabaticGenerator τ H P dP with hG
  set X : ℝ → (E →L[ℂ] E) := fun t => P t * U t - U t * P 0 with hXdef
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun t => (hdP t).continuousAt
  have hGc : Continuous G := by
    have : G = fun t => (-(Complex.I * (τ : ℂ))) • H t + (dP t * P t - P t * dP t) := rfl
    rw [this]
    fun_prop
  have hXd : ∀ t, HasDerivAt X (G t * X t) t := by
    intro t
    have h1 : HasDerivAt (fun u => P u * U u) (dP t * U t + P t * (G t * U t)) t :=
      (hdP t).mul (hU t)
    have h2 : HasDerivAt (fun u => U u * P 0) (G t * U t * P 0) t := (hU t).mul_const (P 0)
    have hint : dP t + P t * G t = G t * P t :=
      adiabaticGenerator_intertwine (τ := τ) hPP hdP hHP hPH t
    have heq : dP t * U t + P t * (G t * U t) - G t * U t * P 0 = G t * X t := by
      have e1 : dP t * U t + P t * (G t * U t) = (dP t + P t * G t) * U t := by noncomm_ring
      rw [e1, hint, hXdef]
      noncomm_ring
    have := h1.sub h2
    rw [heq] at this
    exact this
  have hX0 : X 0 = 0 := by
    simp [hXdef, hU0]
  have := linear_ode_eq_zero hGc hXd hX0 s
  have h := sub_eq_zero.mp (by simpa [hXdef] using this)
  exact h

end Setup

/-- **Adiabatic theorem** (exact, Kato form).

Let `H : ℝ → (E →L[ℂ] E)` be a continuous family of Hamiltonians on a complex normed space `E`,
and let `P s` be the spectral projection onto the instantaneous eigenspace of `H s` belonging to
the eigenvalue `ev s`; this is expressed by `P s * P s = P s` together with
`H s * P s = ev s • P s` and `P s * H s = ev s • P s` (for a nondegenerate eigenvalue `P s` is the
rank-one projection onto the eigenline, but the rank plays no role in the proof).  Assume the
family `s ↦ P s` is continuously differentiable with derivative `dP`.

Let `U` be the adiabatic propagator: the solution of `U'(s) = (-i τ H(s) + [P'(s), P(s)]) U(s)`
with `U 0 = 1`, i.e. the evolution generated by the dynamical phase together with Kato's
geometric (parallel transport) term, which is the exact evolution in the adiabatic limit of a
slowly varying Hamiltonian (`τ` is the slowness parameter).

Then a state `ψ₀` that starts in the eigenspace of `H 0` stays, for all times `s`, in the
*instantaneous* eigenspace of `H s`: it is fixed by `P s` and is an eigenvector of `H s` with the
instantaneous eigenvalue `ev s`.  No transitions out of the eigenspace occur. -/
theorem adiabatic_theorem
    (H P dP U : ℝ → (E →L[ℂ] E)) (ev : ℝ → ℂ) (τ : ℝ)
    (hPP : ∀ s, P s * P s = P s)
    (hdP : ∀ s, HasDerivAt P (dP s) s) (hdPc : Continuous dP)
    (hHc : Continuous H)
    (hHP : ∀ s, H s * P s = ev s • P s) (hPH : ∀ s, P s * H s = ev s • P s)
    (hU0 : U 0 = 1)
    (hU : ∀ s, HasDerivAt U (adiabaticGenerator τ H P dP s * U s) s)
    (psi : E) (hpsi : P 0 psi = psi) (s : ℝ) :
    P s (U s psi) = U s psi ∧ H s (U s psi) = ev s • U s psi := by
  have hint : P s * U s = U s * P 0 :=
    adiabatic_intertwining H P dP U ev τ hPP hdP hdPc hHc hHP hPH hU0 hU s
  have h1 : P s (U s psi) = U s psi := by
    have := congrArg (fun T : E →L[ℂ] E => T psi) hint
    simpa [ContinuousLinearMap.mul_apply, hpsi] using this
  refine ⟨h1, ?_⟩
  have h2 := congrArg (fun T : E →L[ℂ] E => T (U s psi)) (hHP s)
  simpa [ContinuousLinearMap.mul_apply, h1] using h2

/-- Non-vacuity witness: the hypotheses of `Phys.adiabatic_theorem` are satisfiable with a
nonzero Hamiltonian.  Here the Hamiltonian is the constant multiple `e` of the identity on `ℂ`,
`P` is the (rank-one, hence nondegenerate) spectral projection `1`, and the adiabatic propagator
is the dynamical phase `s ↦ e^{-i τ e s}`. -/
theorem adiabatic_hypotheses_satisfiable (e : ℂ) (τ : ℝ) :
    ∃ (H P dP U : ℝ → (ℂ →L[ℂ] ℂ)) (ev : ℝ → ℂ),
      (∀ s, P s * P s = P s) ∧ (∀ s, HasDerivAt P (dP s) s) ∧ Continuous dP ∧ Continuous H ∧
      (∀ s, H s * P s = ev s • P s) ∧ (∀ s, P s * H s = ev s • P s) ∧ U 0 = 1 ∧
      (∀ s, HasDerivAt U (adiabaticGenerator τ H P dP s * U s) s) ∧ H = fun _ => e • 1 := by
  set c : ℂ := -(Complex.I * (τ : ℂ)) * e with hc
  refine ⟨fun _ => e • 1, fun _ => 1, fun _ => 0, fun s => Complex.exp (c * s) • 1, fun _ => e,
    by simp, fun s => hasDerivAt_const _ _, continuous_const, continuous_const, by simp, by simp,
    by simp, ?_, rfl⟩
  intro s
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := s)
  have h2 : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c s := by simpa using h1.const_mul c
  have h3 : HasDerivAt (fun s : ℝ => Complex.exp (c * (s : ℂ))) (Complex.exp (c * s) * c) s :=
    h2.cexp
  have h4 := h3.smul_const (1 : ℂ →L[ℂ] ℂ)
  convert h4 using 1
  simp [adiabaticGenerator, katoGenerator, hc, smul_smul]

end Phys

