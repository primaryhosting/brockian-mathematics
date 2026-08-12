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

import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Statement: The FDT relates linear response to equilibrium correlations.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- Boltzmann weight of the state `w` at inverse temperature `beta` for the
Hamiltonian `E - f • A`, i.e. the unperturbed energy `E` perturbed by an external
field `f` coupled to the observable `A`. -/
noncomputable def weight (beta : ℝ) (E A : Ω → ℝ) (f : ℝ) (w : Ω) : ℝ :=
  Real.exp (-beta * (E w - f * A w))

/-- The partition function of the perturbed system. -/
noncomputable def partition (beta : ℝ) (E A : Ω → ℝ) (f : ℝ) : ℝ :=
  ∑ w, weight beta E A f w

/-- The equilibrium (Gibbs) expectation value of the observable `X` in the
perturbed system. -/
noncomputable def expect (beta : ℝ) (E A : Ω → ℝ) (f : ℝ) (X : Ω → ℝ) : ℝ :=
  (∑ w, X w * weight beta E A f w) / partition beta E A f

lemma weight_pos (beta : ℝ) (E A : Ω → ℝ) (f : ℝ) (w : Ω) :
    0 < weight beta E A f w := Real.exp_pos _

lemma partition_pos [Nonempty Ω] (beta : ℝ) (E A : Ω → ℝ) (f : ℝ) :
    0 < partition beta E A f :=
  Finset.sum_pos (fun w _ => weight_pos beta E A f w) univ_nonempty

lemma hasDerivAt_weight (beta : ℝ) (E A : Ω → ℝ) (f : ℝ) (w : Ω) :
    HasDerivAt (fun f => weight beta E A f w) (beta * A w * weight beta E A f w) f := by
  have h : HasDerivAt (fun f : ℝ => -beta * (E w - f * A w)) (beta * A w) f := by
    have h1 : HasDerivAt (fun y : ℝ => -beta * (E w - y * A w))
        (-beta * -(1 * A w)) f :=
      (((hasDerivAt_id f).mul_const (A w)).const_sub (E w)).const_mul (-beta)
    convert h1 using 1; ring
  have h2 := h.exp
  simpa [weight, mul_comm] using h2

lemma hasDerivAt_weighted_sum (beta : ℝ) (E A : Ω → ℝ) (X : Ω → ℝ) (f : ℝ) :
    HasDerivAt (fun f => ∑ w, X w * weight beta E A f w)
      (∑ w, beta * (A w * X w) * weight beta E A f w) f := by
  apply HasDerivAt.fun_sum
  intro w _
  have h := (hasDerivAt_weight beta E A f w).const_mul (X w)
  convert h using 1
  ring

lemma hasDerivAt_partition (beta : ℝ) (E A : Ω → ℝ) (f : ℝ) :
    HasDerivAt (fun f => partition beta E A f)
      (∑ w, beta * A w * weight beta E A f w) f := by
  apply HasDerivAt.fun_sum
  intro w _
  exact hasDerivAt_weight beta E A f w

/-- **Fluctuation–dissipation theorem** (static, classical form).

For a finite classical system with energy `E` at inverse temperature `beta`,
perturbed by an external field `f` coupled to the observable `A`, the linear
response of any observable `B` — the derivative of its equilibrium expectation
value with respect to the field — equals `beta` times the equilibrium covariance
(the correlation of the fluctuations) of `A` and `B`:

`d⟨B⟩_f / df = beta * (⟨A·B⟩_f - ⟨A⟩_f ⟨B⟩_f)`. -/
theorem fluctuation_dissipation [Nonempty Ω] (beta : ℝ) (E A B : Ω → ℝ) (f : ℝ) :
    HasDerivAt (fun f => expect beta E A f B)
      (beta * (expect beta E A f (fun w => A w * B w)
        - expect beta E A f A * expect beta E A f B)) f := by
  have hZ := partition_pos (Ω := Ω) beta E A f
  have hnum := hasDerivAt_weighted_sum beta E A B f
  have hden := hasDerivAt_partition beta E A f
  have h := hnum.div hden hZ.ne'
  have key : ((∑ w, beta * (A w * B w) * weight beta E A f w) * partition beta E A f
      - (∑ w, B w * weight beta E A f w) * (∑ w, beta * A w * weight beta E A f w))
        / partition beta E A f ^ 2
      = beta * (expect beta E A f (fun w => A w * B w)
        - expect beta E A f A * expect beta E A f B) := by
    have h1 : (∑ w, beta * (A w * B w) * weight beta E A f w)
        = beta * ∑ w, (A w * B w) * weight beta E A f w := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
    have h2 : (∑ w, beta * A w * weight beta E A f w)
        = beta * ∑ w, A w * weight beta E A f w := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
    rw [h1, h2]
    simp only [expect]
    field_simp
  rw [← key]
  exact h

end Phys

