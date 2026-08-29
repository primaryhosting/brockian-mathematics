/-
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

variable {ι : Type*} [Fintype ι]

/-- Boltzmann weight of the microstate `i` for the perturbed Hamiltonian
`E i - f * B i` at inverse temperature `beta`. -/
noncomputable def weight (beta : ℝ) (E B : ι → ℝ) (f : ℝ) (i : ι) : ℝ :=
  Real.exp (-beta * (E i - f * B i))

/-- Partition function of the perturbed system. -/
noncomputable def Zpart (beta : ℝ) (E B : ι → ℝ) (f : ℝ) : ℝ :=
  ∑ i, weight beta E B f i

/-- Equilibrium (canonical) expectation value of the observable `A`
in the system perturbed by `-f * B`. -/
noncomputable def mean (beta : ℝ) (E B : ι → ℝ) (A : ι → ℝ) (f : ℝ) : ℝ :=
  (∑ i, A i * weight beta E B f i) / Zpart beta E B f

omit [Fintype ι] in
lemma weight_pos (beta : ℝ) (E B : ι → ℝ) (f : ℝ) (i : ι) : 0 < weight beta E B f i :=
  Real.exp_pos _

lemma Zpart_pos [Nonempty ι] (beta : ℝ) (E B : ι → ℝ) (f : ℝ) : 0 < Zpart beta E B f :=
  Finset.sum_pos (fun i _ => weight_pos beta E B f i) Finset.univ_nonempty

omit [Fintype ι] in
lemma hasDerivAt_weight (beta : ℝ) (E B : ι → ℝ) (i : ι) :
    HasDerivAt (fun f => weight beta E B f i) (beta * B i * weight beta E B 0 i) 0 := by
  have h1 : HasDerivAt (fun f : ℝ => -beta * (E i - f * B i)) (beta * B i) 0 := by
    have h0 : HasDerivAt (fun f : ℝ => E i - f * B i) (-B i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (B i)).const_sub (E i)
    have := h0.const_mul (-beta)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have := h1.exp
  simpa [weight, mul_comm, mul_left_comm, mul_assoc] using this

lemma hasDerivAt_numer (beta : ℝ) (E B A : ι → ℝ) :
    HasDerivAt (fun f => ∑ i, A i * weight beta E B f i)
      (∑ i, A i * (beta * B i * weight beta E B 0 i)) 0 := by
  simpa [Finset.sum_apply] using
    HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => (hasDerivAt_weight beta E B i).const_mul (A i))

lemma hasDerivAt_Zpart (beta : ℝ) (E B : ι → ℝ) :
    HasDerivAt (fun f => Zpart beta E B f)
      (∑ i, beta * B i * weight beta E B 0 i) 0 := by
  simpa [Zpart, Finset.sum_apply] using
    HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hasDerivAt_weight beta E B i)

/-- **Fluctuation–dissipation theorem** (classical, static form).

For a finite classical system in canonical equilibrium at inverse temperature `beta`
with energies `E`, the linear response of the observable `A` to a perturbation
`E i ↦ E i - f * B i` of the Hamiltonian equals `beta` times the equilibrium
covariance (the fluctuation) of `A` and `B`:

`d/df ⟨A⟩_f |_{f=0} = beta * (⟨A B⟩ - ⟨A⟩ ⟨B⟩)`. -/
theorem fluctuation_dissipation [Nonempty ι] (beta : ℝ) (E B A : ι → ℝ) :
    HasDerivAt (fun f => mean beta E B A f)
      (beta * (mean beta E B (fun i => A i * B i) 0
        - mean beta E B A 0 * mean beta E B B 0)) 0 := by
  have hZ := hasDerivAt_Zpart beta E B
  have hN := hasDerivAt_numer beta E B A
  have hZne : Zpart beta E B 0 ≠ 0 := ne_of_gt (Zpart_pos beta E B 0)
  have hdiv := hN.div hZ hZne
  refine hdiv.congr_deriv ?_
  have e1 : ∑ i, A i * (beta * B i * weight beta E B 0 i)
      = beta * ∑ i, (A i * B i) * weight beta E B 0 i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have e2 : ∑ i, beta * B i * weight beta E B 0 i
      = beta * ∑ i, B i * weight beta E B 0 i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e1, e2]
  simp only [mean, Zpart]
  field_simp

/-- Derivative form of the fluctuation–dissipation theorem: the static susceptibility
`d⟨A⟩/df` at zero field equals `beta` times the equilibrium covariance of `A` and `B`. -/
theorem fluctuation_dissipation_deriv [Nonempty ι] (beta : ℝ) (E B A : ι → ℝ) :
    deriv (fun f => mean beta E B A f) 0
      = beta * (mean beta E B (fun i => A i * B i) 0
        - mean beta E B A 0 * mean beta E B B 0) :=
  (fluctuation_dissipation beta E B A).deriv

end Phys

