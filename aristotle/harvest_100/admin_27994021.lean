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

namespace QPhys

open NormedSpace

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-- The time-evolution operator `U(t) = exp (-i H t / ℏ)` associated to a Hamiltonian `H`
in a complex Banach `*`-algebra (e.g. the bounded operators on a Hilbert space). -/
noncomputable def timeEvolution (hbar : ℝ) (H : A) (t : ℝ) : A :=
  exp (((-Complex.I) * (t / hbar)) • H)

omit [ContinuousStar A] [CompleteSpace A] in
/-- For a self-adjoint `H`, the element `(-i t/ℏ) • H` is skew-adjoint. -/
theorem smul_mem_skewAdjoint_of_isSelfAdjoint (hbar : ℝ) {H : A} (hH : IsSelfAdjoint H) (t : ℝ) :
    ((-Complex.I) * (t / hbar) : ℂ) • H ∈ skewAdjoint A := by
  rw [skewAdjoint.mem_iff, star_smul, hH.star_eq, ← neg_smul]
  congr 1
  simp

/-- **Unitarity of time evolution**: for a self-adjoint Hamiltonian `H`, the operator
`U(t) = exp (-i H t / ℏ)` is unitary for every real time `t`. -/
theorem unitary_time_evolution (hbar : ℝ) {H : A} (hH : IsSelfAdjoint H) (t : ℝ) :
    timeEvolution hbar H t ∈ unitary A := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  exact exp_mem_unitary_of_mem_skewAdjoint
    (smul_mem_skewAdjoint_of_isSelfAdjoint hbar hH t)

/-- Explicit form of unitarity: `U(t)⋆ * U(t) = 1` and `U(t) * U(t)⋆ = 1`. -/
theorem star_mul_timeEvolution (hbar : ℝ) {H : A} (hH : IsSelfAdjoint H) (t : ℝ) :
    star (timeEvolution hbar H t) * timeEvolution hbar H t = 1 ∧
      timeEvolution hbar H t * star (timeEvolution hbar H t) = 1 :=
  Unitary.mem_iff.mp (unitary_time_evolution hbar hH t)

end Algebra

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- On a complex Hilbert space, the time-evolution operator of a self-adjoint (bounded)
Hamiltonian is unitary, i.e. `U(t)† U(t) = U(t) U(t)† = 1`. -/
theorem unitary_time_evolution_clm (hbar : ℝ) {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) (t : ℝ) :
    timeEvolution hbar H t ∈ unitary (E →L[ℂ] E) :=
  unitary_time_evolution hbar hH t

/-- Time evolution preserves inner products (hence probabilities). -/
theorem inner_timeEvolution (hbar : ℝ) {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) (t : ℝ)
    (x y : E) :
    inner ℂ (timeEvolution hbar H t x) (timeEvolution hbar H t y) = inner ℂ x y := by
  have h := (Unitary.mem_iff.mp (unitary_time_evolution_clm hbar hH t)).1
  have : (ContinuousLinearMap.adjoint (timeEvolution hbar H t)).comp
      (timeEvolution hbar H t) = ContinuousLinearMap.id ℂ E := h
  calc inner ℂ (timeEvolution hbar H t x) (timeEvolution hbar H t y)
      = inner ℂ x (ContinuousLinearMap.adjoint (timeEvolution hbar H t)
          (timeEvolution hbar H t y)) := by
        rw [ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ x y := by
        rw [show ContinuousLinearMap.adjoint (timeEvolution hbar H t)
            (timeEvolution hbar H t y) = y from congrArg (fun f => f y) this]

/-- Time evolution is norm preserving. -/
theorem norm_timeEvolution_apply (hbar : ℝ) {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) (t : ℝ)
    (x : E) : ‖timeEvolution hbar H t x‖ = ‖x‖ := by
  have := inner_timeEvolution hbar hH t x x
  have h1 : ‖timeEvolution hbar H t x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    exact_mod_cast congrArg Complex.re this
  have h2 : (0:ℝ) ≤ ‖timeEvolution hbar H t x‖ := norm_nonneg _
  nlinarith [norm_nonneg x]

end Hilbert

end QPhys

