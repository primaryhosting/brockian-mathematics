/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The expectation value `⟨A⟩ (t) = ⟪ψ t, A t (ψ t)⟫` of a (possibly time-dependent)
observable `A` in the state `ψ t`. -/
noncomputable def expVal (psi : ℝ → E) (A : ℝ → (E →L[ℂ] E)) (t : ℝ) : ℂ :=
  inner ℂ (psi t) (A t (psi t))

/-- The commutator `[H, A] = H A - A H` of two operators. -/
noncomputable def commutator (H A : E →L[ℂ] E) : E →L[ℂ] E := H.comp A - A.comp H

/-- **Ehrenfest theorem** (derivative form).

If `ψ` solves the Schrödinger equation `iℏ ψ' = H ψ`, i.e. `ψ' = (-i/ℏ) H ψ`, with `H` a
symmetric (self-adjoint) operator, and if the time-dependent observable `A` is differentiable
at `t` with derivative `∂A/∂t = A' t`, then the expectation value `⟨A⟩` has derivative
`(i/ℏ) ⟪ψ, [H, A] ψ⟫ + ⟪ψ, (∂A/∂t) ψ⟫` at `t`. -/
theorem ehrenfest_hasDerivAt
    (hbar : ℝ) (H : E →L[ℂ] E)
    (hH : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (psi : ℝ → E) (A A' : ℝ → (E →L[ℂ] E)) (t : ℝ)
    (hpsi : HasDerivAt psi ((-Complex.I / (hbar : ℂ)) • H (psi t)) t)
    (hA : HasDerivAt A (A' t) t) :
    HasDerivAt (expVal psi A)
      ((Complex.I / (hbar : ℂ)) * inner ℂ (psi t) (commutator H (A t) (psi t))
        + inner ℂ (psi t) (A' t (psi t))) t := by
  have hAR : HasDerivAt (fun s => (A s).restrictScalars ℝ) ((A' t).restrictScalars ℝ) t :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hA
  have hf : HasDerivAt (fun s => A s (psi s))
      ((A' t) (psi t) + (A t) ((-Complex.I / (hbar : ℂ)) • H (psi t))) t := hAR.clm_apply hpsi
  have h := hpsi.inner ℂ hf
  convert h using 1
  simp [commutator, inner_add_right, inner_smul_right, inner_smul_left,
    ContinuousLinearMap.coe_sub', hH]
  ring

/-- **Ehrenfest theorem**: `d⟨A⟩/dt = (i/ℏ)⟪ψ, [H, A]ψ⟫ + ⟪ψ, (∂A/∂t)ψ⟫`,
for a state `ψ` evolving by the Schrödinger equation `iℏ ψ' = H ψ` with symmetric
Hamiltonian `H`, and a time-dependent observable `A` with time derivative `A'`. -/
theorem ehrenfest
    (hbar : ℝ) (H : E →L[ℂ] E)
    (hH : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (psi : ℝ → E) (A A' : ℝ → (E →L[ℂ] E)) (t : ℝ)
    (hpsi : HasDerivAt psi ((-Complex.I / (hbar : ℂ)) • H (psi t)) t)
    (hA : HasDerivAt A (A' t) t) :
    deriv (expVal psi A) t =
      (Complex.I / (hbar : ℂ)) * inner ℂ (psi t) (commutator H (A t) (psi t))
        + inner ℂ (psi t) (A' t (psi t)) :=
  (ehrenfest_hasDerivAt hbar H hH psi A A' t hpsi hA).deriv

/-- Ehrenfest theorem for a time-independent observable `A`:
`d⟨A⟩/dt = (i/ℏ)⟪ψ, [H, A]ψ⟫`. -/
theorem ehrenfest_timeIndependent
    (hbar : ℝ) (H : E →L[ℂ] E)
    (hH : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (psi : ℝ → E) (A : E →L[ℂ] E) (t : ℝ)
    (hpsi : HasDerivAt psi ((-Complex.I / (hbar : ℂ)) • H (psi t)) t) :
    deriv (expVal psi (fun _ => A)) t =
      (Complex.I / (hbar : ℂ)) * inner ℂ (psi t) (commutator H A (psi t)) := by
  have h := ehrenfest hbar H hH psi (fun _ => A) (fun _ => 0) t hpsi (hasDerivAt_const t A)
  simpa using h

/-- The hypotheses of `ehrenfest` are non-vacuous: on the one-dimensional Hilbert space `ℂ`,
with Hamiltonian `H = e` (multiplication by a real energy `e`), the state
`ψ t = exp(-i e t/ℏ) ψ₀` solves the Schrödinger equation, and the observable `A t = t`
is a genuinely time-dependent differentiable family with nonzero time derivative. -/
theorem ehrenfest_hypotheses_satisfiable (hbar e : ℝ) (z0 : ℂ) (hz : z0 ≠ 0) :
    ∃ (H : ℂ →L[ℂ] ℂ) (psi : ℝ → ℂ) (A A' : ℝ → (ℂ →L[ℂ] ℂ)),
      (∀ x y : ℂ, inner ℂ (H x) y = inner ℂ x (H y)) ∧
      (∀ t, psi t ≠ 0) ∧
      (∀ t, HasDerivAt psi ((-Complex.I / (hbar : ℂ)) • H (psi t)) t) ∧
      (∀ t, HasDerivAt A (A' t) t) ∧
      (∀ t, A' t ≠ 0) := by
  refine ⟨(e : ℂ) • ContinuousLinearMap.id ℂ ℂ,
    fun s : ℝ => Complex.exp ((-Complex.I * e / (hbar : ℂ)) * (s : ℂ)) * z0,
    fun s : ℝ => (s : ℂ) • ContinuousLinearMap.id ℂ ℂ,
    fun _ => ContinuousLinearMap.id ℂ ℂ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp [mul_comm, mul_assoc]
  · intro t
    exact mul_ne_zero (Complex.exp_ne_zero _) hz
  · intro t
    have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ))) 1 t := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => (-Complex.I * e / (hbar : ℂ)) * (s : ℂ))
        (-Complex.I * e / (hbar : ℂ)) t := by
      simpa using h1.const_mul (-Complex.I * e / (hbar : ℂ))
    have h3 := (h2.cexp).mul_const z0
    convert h3 using 1
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  · intro t
    have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ))) 1 t := Complex.ofRealCLM.hasDerivAt
    simpa using h1.smul_const (ContinuousLinearMap.id ℂ ℂ)
  · intro t h
    have h1 : (1 : ℂ) = 0 := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) h
    exact one_ne_zero h1

end QPhys

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

