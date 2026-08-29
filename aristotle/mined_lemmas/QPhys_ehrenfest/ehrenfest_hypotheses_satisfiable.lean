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

