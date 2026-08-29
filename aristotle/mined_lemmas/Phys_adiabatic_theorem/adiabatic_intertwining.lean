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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Kato's adiabatic generator associated with a smooth family of spectral projections
`P` with derivative `P'`: `K(s) = [P'(s), P(s)] = P'(s)P(s) - P(s)P'(s)`. -/

theorem adiabatic_intertwining
    (hproj : ∀ s, P s * P s = P s)
    (hP : ∀ s, HasDerivAt P (P' s) s)
    (hP'cont : Continuous P')
    (hphase : Continuous phase)
    (hU : ∀ s, HasDerivAt U (adiabaticGen phase P P' s * U s) s)
    (hU0 : U 0 = 1) {s : ℝ} (hs : 0 ≤ s) :
    P s * U s = U s * P 0 := by
  classical
  have hPcont : Continuous P :=
    continuous_iff_continuousAt.2 fun t => (hP t).continuousAt
  have hUcont : Continuous U :=
    continuous_iff_continuousAt.2 fun t => (hU t).continuousAt
  set G : ℝ → (E →L[ℂ] E) := adiabaticGen phase P P' with hG
  have hGcont : Continuous G := by
    have : Continuous fun t => (phase t) • (1 : E →L[ℂ] E) :=
      hphase.smul continuous_const
    simpa [hG, adiabaticGen, katoGen] using
      this.add ((hP'cont.mul hPcont).sub (hPcont.mul hP'cont))
  set V : ℝ → (E →L[ℂ] E) := fun t => P t * U t - U t * P 0 with hV
  have hVderiv : ∀ t, HasDerivAt V (G t * V t) t := by
    intro t
    have h1 : HasDerivAt (fun r => P r * U r) (P' t * U t + P t * (G t * U t)) t :=
      (hP t).mul (hU t)
    have h2 : HasDerivAt (fun r => U r * P 0) (G t * U t * P 0 + U t * 0) t :=
      (hU t).mul (hasDerivAt_const t (P 0))
    have h3 := h1.sub h2
    have key : P' t * U t + P t * (G t * U t) - (G t * U t * P 0 + U t * 0) = G t * V t := by
      have hcomm := deriv_eq_commutator_katoGen hproj hP t
      have step : P' t * U t + P t * (katoGen P P' t * U t)
          = katoGen P P' t * (P t * U t) := by
        rw [← hcomm]
        simp only [sub_mul, mul_assoc]
        abel
      have expand : ∀ X : E →L[ℂ] E,
          G t * X = (phase t) • X + katoGen P P' t * X := by
        intro X
        rw [hG]
        simp only [adiabaticGen, add_mul, smul_mul_assoc, one_mul]
      simp only [hV, expand]
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub, mul_sub,
        mul_zero, add_zero, mul_assoc]
      linear_combination (norm := module) step
    have h4 : HasDerivAt V
        (P' t * U t + P t * (G t * U t) - (G t * U t * P 0 + U t * 0)) t := h3
    rw [key] at h4
    exact h4
  have hV0 : V 0 = 0 := by simp [hV, hU0]
  -- Grönwall on `[0, s]`
  obtain ⟨C, hC⟩ : ∃ C, ∀ t ∈ Icc (0 : ℝ) s, ‖G t‖ ≤ C :=
    (isCompact_Icc).exists_bound_of_continuousOn hGcont.continuousOn
  have hVcont : ContinuousOn V (Icc 0 s) :=
    (Continuous.continuousOn (by
      have : Continuous fun t => P t * U t := hPcont.mul hUcont
      exact this.sub (hUcont.mul continuous_const)))
  have hzero : ∀ t ∈ Icc (0 : ℝ) s, V t = 0 := by
    refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := C)
      hVcont (fun t _ => (hVderiv t).hasDerivWithinAt) hV0 ?_
    intro t ht
    calc ‖G t * V t‖ ≤ ‖G t‖ * ‖V t‖ := norm_mul_le _ _
      _ ≤ C * ‖V t‖ := by
          exact mul_le_mul_of_nonneg_right (hC t (Ico_subset_Icc_self ht)) (norm_nonneg _)
  have := hzero s (right_mem_Icc.2 hs)
  have := sub_eq_zero.mp this
  simpa [hV] using this

/-- **Adiabatic theorem.**

Let `H : ℝ → (E →L[ℂ] E)` be a time-dependent Hamiltonian, and let `P s` be the (rank-one,
in the nondegenerate case) spectral projection onto the instantaneous eigenspace of `H s`
for the instantaneous eigenvalue `Energy s`, depending differentiably on `s`.

Let `U` be the adiabatic propagator: the solution of the Schrödinger-type equation
`U'(s) = (phase s • 1 + [P'(s), P(s)]) U(s)`, `U 0 = 1`, whose generator consists of the
scalar dynamical/geometric phase together with Kato's geometric generator; this is the exact
generator of the slow (adiabatic) limit of the dynamics.

Then a state `ψ` which is initially in the eigenspace of `H 0` remains, at every later time
`s`, an eigenvector of the instantaneous Hamiltonian `H s` with the instantaneous eigenvalue
`Energy s`: the state never leaks out of the instantaneous eigenspace. -/
