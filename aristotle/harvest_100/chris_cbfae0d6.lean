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

/-
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a
-- module docstring to precede the `import` line.)

import Mathlib

namespace Phys

open Finset

variable {ι : Type*} [Fintype ι]

/-- Boltzmann weight of state `i` for the Hamiltonian `E - f • A` at inverse
temperature `beta`, i.e. `exp (-beta * (E i - f * A i))`. -/
noncomputable def weight (beta : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) : ℝ :=
  Real.exp (beta * (f * A i - E i))

/-- Partition function `Z(f) = ∑ i, exp (-beta * (E i - f * A i))`. -/
noncomputable def partition (beta : ℝ) (E A : ι → ℝ) (f : ℝ) : ℝ :=
  ∑ i, weight beta E A f i

/-- Canonical (Gibbs) expectation value of an observable `g` in the perturbed
ensemble with field strength `f`. -/
noncomputable def expect (beta : ℝ) (E A : ι → ℝ) (f : ℝ) (g : ι → ℝ) : ℝ :=
  (∑ i, g i * weight beta E A f i) / partition beta E A f

omit [Fintype ι] in
lemma weight_pos (beta : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) :
    0 < weight beta E A f i := Real.exp_pos _

lemma partition_pos [Nonempty ι] (beta : ℝ) (E A : ι → ℝ) (f : ℝ) :
    0 < partition beta E A f :=
  Finset.sum_pos (fun i _ => weight_pos beta E A f i) Finset.univ_nonempty

omit [Fintype ι] in
lemma hasDerivAt_weight (beta : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) :
    HasDerivAt (fun f => weight beta E A f i) (beta * A i * weight beta E A f i) f := by
  have h : HasDerivAt (fun f : ℝ => beta * (f * A i - E i)) (beta * A i) f := by
    simpa using (((hasDerivAt_id f).mul_const (A i)).sub_const (E i)).const_mul beta
  simpa [weight, mul_comm] using h.exp

lemma hasDerivAt_numer (beta : ℝ) (E A : ι → ℝ) (g : ι → ℝ) (f : ℝ) :
    HasDerivAt (fun f => ∑ i, g i * weight beta E A f i)
      (beta * ∑ i, (A i * g i) * weight beta E A f i) f := by
  have h : HasDerivAt (fun f => ∑ i, g i * weight beta E A f i)
      (∑ i, g i * (beta * A i * weight beta E A f i)) f :=
    HasDerivAt.fun_sum (fun i _ => (hasDerivAt_weight beta E A f i).const_mul (g i))
  refine h.congr_deriv ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Fluctuation–dissipation theorem (static / classical linear response).**

For a classical system with energy levels `E` in the canonical ensemble at inverse
temperature `beta`, perturbed by a field `f` coupling to the observable `A`
(so the energy is `E i - f * A i`), the response of the equilibrium average of any
observable `B` to the field is `beta` times the equilibrium covariance of `A` and `B`:

  `d⟨B⟩/df = beta * (⟨A B⟩ - ⟨A⟩⟨B⟩)`.

Dissipation (the left-hand side, the susceptibility) is thus determined by the
equilibrium fluctuations (the right-hand side). -/
theorem fluctuation_dissipation [Nonempty ι] (beta : ℝ) (E A B : ι → ℝ) (f : ℝ) :
    HasDerivAt (fun f => expect beta E A f B)
      (beta * (expect beta E A f (fun i => A i * B i)
        - expect beta E A f A * expect beta E A f B)) f := by
  have hZ : partition beta E A f ≠ 0 := (partition_pos beta E A f).ne'
  have hN := hasDerivAt_numer beta E A B f
  have hD : HasDerivAt (fun f => partition beta E A f)
      (beta * ∑ i, (A i * 1) * weight beta E A f i) f := by
    simpa [partition] using hasDerivAt_numer beta E A (fun _ => 1) f
  have h := hN.div hD hZ
  refine h.congr_deriv ?_
  simp only [expect, partition, mul_one]
  field_simp

/-- The fluctuation–dissipation theorem in terms of `deriv`: the susceptibility
`χ = d⟨B⟩/df` equals `beta` times the equilibrium covariance `⟨A B⟩ - ⟨A⟩⟨B⟩`. -/
theorem fluctuation_dissipation_deriv [Nonempty ι] (beta : ℝ) (E A B : ι → ℝ) (f : ℝ) :
    deriv (fun f => expect beta E A f B) f
      = beta * (expect beta E A f (fun i => A i * B i)
        - expect beta E A f A * expect beta E A f B) :=
  (fluctuation_dissipation beta E A B f).deriv

end Phys

