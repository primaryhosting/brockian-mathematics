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

variable {ι : Type*} [Fintype ι]

/-- Unnormalised Gibbs weight `exp (-β Eᵢ)` of the state `i`. -/
noncomputable def gibbsWeight (beta : ℝ) (E : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (-beta * E i)

/-- The partition function `Z = ∑ᵢ exp (-β Eᵢ)`. -/
noncomputable def partition (beta : ℝ) (E : ι → ℝ) : ℝ :=
  ∑ i, gibbsWeight beta E i

/-- Equilibrium (Gibbs) expectation value of the observable `X`. -/
noncomputable def gibbsExpect (beta : ℝ) (E X : ι → ℝ) : ℝ :=
  (∑ i, X i * gibbsWeight beta E i) / partition beta E

omit [Fintype ι] in
lemma gibbsWeight_pos (beta : ℝ) (E : ι → ℝ) (i : ι) : 0 < gibbsWeight beta E i :=
  Real.exp_pos _

lemma partition_pos [Nonempty ι] (beta : ℝ) (E : ι → ℝ) : 0 < partition beta E :=
  Finset.sum_pos (fun i _ => gibbsWeight_pos beta E i) univ_nonempty

omit [Fintype ι] in
/-- Derivative in the field strength `f` of the perturbed Boltzmann weight
`exp (-β (Eᵢ - f Aᵢ))` at `f = 0`. -/
lemma hasDerivAt_weight (beta : ℝ) (E A : ι → ℝ) (i : ι) :
    HasDerivAt (fun f : ℝ => Real.exp (-beta * (E i - f * A i)))
      (beta * A i * gibbsWeight beta E i) 0 := by
  have h1 : HasDerivAt (fun f : ℝ => -beta * (E i - f * A i)) (beta * A i) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (A i)).const_sub (E i)).const_mul (-beta)
  have h2 := h1.exp
  simpa [gibbsWeight, mul_comm] using h2

/-- **Classical (static) fluctuation–dissipation theorem.**

For a finite classical system with energies `E` in thermal equilibrium at inverse
temperature `β`, perturb the Hamiltonian by a field conjugate to the observable `A`,
`E ↦ E - f A`.  Then the linear response of the equilibrium average of any observable
`B` to the field `f` equals `β` times the equilibrium correlation (covariance) of `A`
and `B`:

`d/df ⟨B⟩_f |_{f=0} = β (⟨A B⟩ - ⟨A⟩⟨B⟩)`. -/
theorem fluctuation_dissipation [Nonempty ι] (beta : ℝ) (E A B : ι → ℝ) :
    HasDerivAt
      (fun f : ℝ =>
        (∑ i, B i * Real.exp (-beta * (E i - f * A i))) /
          (∑ i, Real.exp (-beta * (E i - f * A i))))
      (beta * (gibbsExpect beta E (fun i => A i * B i)
        - gibbsExpect beta E A * gibbsExpect beta E B)) 0 := by
  set Z : ℝ := partition beta E with hZdef
  have hZpos : 0 < Z := partition_pos beta E
  -- numerator and denominator derivatives
  have hN : HasDerivAt (fun f : ℝ => ∑ i, B i * Real.exp (-beta * (E i - f * A i)))
      (∑ i, B i * (beta * A i * gibbsWeight beta E i)) 0 := by
    have hfun : (fun f : ℝ => ∑ i, B i * Real.exp (-beta * (E i - f * A i)))
        = ∑ i ∈ (univ : Finset ι), (fun f : ℝ => B i * Real.exp (-beta * (E i - f * A i))) := by
      funext f; simp
    rw [hfun]
    exact HasDerivAt.sum (fun i _ => (hasDerivAt_weight beta E A i).const_mul (B i))
  have hD : HasDerivAt (fun f : ℝ => ∑ i, Real.exp (-beta * (E i - f * A i)))
      (∑ i, beta * A i * gibbsWeight beta E i) 0 := by
    have hfun : (fun f : ℝ => ∑ i, Real.exp (-beta * (E i - f * A i)))
        = ∑ i ∈ (univ : Finset ι), (fun f : ℝ => Real.exp (-beta * (E i - f * A i))) := by
      funext f; simp
    rw [hfun]
    exact HasDerivAt.sum (fun i _ => hasDerivAt_weight beta E A i)
  have hD0 : (∑ i, Real.exp (-beta * (E i - (0 : ℝ) * A i))) = Z := by
    simp [hZdef, partition, gibbsWeight]
  have hne : (∑ i, Real.exp (-beta * (E i - (0 : ℝ) * A i))) ≠ 0 := by
    rw [hD0]; exact ne_of_gt hZpos
  have hdiv := hN.div hD hne
  convert hdiv using 1
  -- now identify the two expressions for the derivative
  have hN0 : (∑ i, B i * Real.exp (-beta * (E i - (0 : ℝ) * A i)))
      = ∑ i, B i * gibbsWeight beta E i := by
    simp [gibbsWeight]
  have e1 : (∑ i, B i * (beta * A i * gibbsWeight beta E i))
      = beta * ∑ i, (A i * B i) * gibbsWeight beta E i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have e2 : (∑ i, beta * A i * gibbsWeight beta E i)
      = beta * ∑ i, A i * gibbsWeight beta E i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hD0, hN0, e1, e2]
  simp only [gibbsExpect, ← hZdef]
  field_simp

end Phys

