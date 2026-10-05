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

import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {ι : Type*} [Fintype ι]

/-- The Boltzmann weight `exp (-β (E i - λ A i))` of the microstate `i`, for the
Hamiltonian `E` perturbed by the field `λ` coupled to the observable `A`. -/
noncomputable def boltzmannWeight (beta : ℝ) (E A : ι → ℝ) (lam : ℝ) (i : ι) : ℝ :=
  Real.exp (-beta * (E i - lam * A i))

/-- The partition function of the perturbed system. -/
noncomputable def partition (beta : ℝ) (E A : ι → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, boltzmannWeight beta E A lam i

/-- The equilibrium (Gibbs) expectation value of an observable `f` in the
perturbed system. -/
noncomputable def expect (beta : ℝ) (E A : ι → ℝ) (lam : ℝ) (f : ι → ℝ) : ℝ :=
  (∑ i, f i * boltzmannWeight beta E A lam i) / partition beta E A lam

omit [Fintype ι] in
lemma boltzmannWeight_pos (beta : ℝ) (E A : ι → ℝ) (lam : ℝ) (i : ι) :
    0 < boltzmannWeight beta E A lam i := Real.exp_pos _

lemma partition_pos [Nonempty ι] (beta : ℝ) (E A : ι → ℝ) (lam : ℝ) :
    0 < partition beta E A lam :=
  Finset.sum_pos (fun i _ => boltzmannWeight_pos beta E A lam i) univ_nonempty

omit [Fintype ι] in
lemma hasDerivAt_boltzmannWeight (beta : ℝ) (E A : ι → ℝ) (i : ι) (lam : ℝ) :
    HasDerivAt (fun l => boltzmannWeight beta E A l i)
      (beta * A i * boltzmannWeight beta E A lam i) lam := by
  have h : HasDerivAt (fun l : ℝ => -beta * (E i - l * A i)) (beta * A i) lam := by
    have h0 : HasDerivAt (fun l : ℝ => -beta * (E i - l * A i))
        (-beta * -(1 * A i)) lam :=
      (((hasDerivAt_id lam).mul_const (A i)).const_sub (E i)).const_mul (-beta)
    simpa using h0
  simpa [boltzmannWeight, mul_comm] using h.exp

/-- **Static fluctuation–dissipation theorem (Kubo).**

For a finite classical system with energies `E`, in equilibrium at inverse
temperature `β`, perturb the Hamiltonian by `-λ A`.  Then the linear response
(susceptibility) of the observable `A` to the field `λ`, i.e. the derivative at
`λ = 0` of the equilibrium expectation `⟨A⟩_λ`, equals `β` times the equilibrium
fluctuation `⟨A²⟩ - ⟨A⟩²` of `A` in the unperturbed system.

The analytic content is the quotient rule `HasDerivAt.div` applied to
`⟨A⟩_λ = (∑ i, A i * w i λ) / (∑ i, w i λ)`. -/
theorem fluctuation_dissipation [Nonempty ι] (beta : ℝ) (E A : ι → ℝ) :
    HasDerivAt (fun lam => expect beta E A lam A)
      (beta * (expect beta E A 0 (fun i => A i ^ 2) - (expect beta E A 0 A) ^ 2)) 0 := by
  set w : ι → ℝ := fun i => boltzmannWeight beta E A 0 i with hw
  have hD : HasDerivAt (fun l => partition beta E A l) (∑ i, beta * A i * w i) 0 := by
    have := HasDerivAt.sum (u := (univ : Finset ι)) (x := (0 : ℝ))
      (A := fun i l => boltzmannWeight beta E A l i)
      (A' := fun i => beta * A i * w i)
      (fun i _ => hasDerivAt_boltzmannWeight beta E A i 0)
    have e : (∑ i : ι, fun l : ℝ => boltzmannWeight beta E A l i)
        = fun l : ℝ => partition beta E A l := by
      funext l; simp [partition, Finset.sum_apply]
    rwa [e] at this
  have hN : HasDerivAt (fun l => ∑ i, A i * boltzmannWeight beta E A l i)
      (∑ i, A i * (beta * A i * w i)) 0 := by
    have := HasDerivAt.sum (u := (univ : Finset ι)) (x := (0 : ℝ))
      (A := fun i l => A i * boltzmannWeight beta E A l i)
      (A' := fun i => A i * (beta * A i * w i))
      (fun i _ => (hasDerivAt_boltzmannWeight beta E A i 0).const_mul (A i))
    have e : (∑ i : ι, fun l : ℝ => A i * boltzmannWeight beta E A l i)
        = fun l : ℝ => ∑ i, A i * boltzmannWeight beta E A l i := by
      funext l; simp [Finset.sum_apply]
    rwa [e] at this
  have hZ : partition beta E A 0 ≠ 0 := (partition_pos beta E A 0).ne'
  have hdiv := hN.div hD hZ
  refine hdiv.congr_deriv ?_
  have h1 : (∑ i, A i * (beta * A i * w i)) = beta * ∑ i, A i ^ 2 * w i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : (∑ i, beta * A i * w i) = beta * ∑ i, A i * w i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2]
  simp only [expect]
  field_simp
  ring

/-- Variance form of the fluctuation-dissipation theorem: the susceptibility is
`β` times the equilibrium variance `⟨(A - ⟨A⟩)²⟩` of the observable. -/
theorem fluctuation_dissipation_variance [Nonempty ι] (beta : ℝ) (E A : ι → ℝ) :
    HasDerivAt (fun lam => expect beta E A lam A)
      (beta * expect beta E A 0 (fun i => (A i - expect beta E A 0 A) ^ 2)) 0 := by
  have hZ : partition beta E A 0 ≠ 0 := (partition_pos beta E A 0).ne'
  set m : ℝ := expect beta E A 0 A with hm
  have key : expect beta E A 0 (fun i => (A i - m) ^ 2)
      = expect beta E A 0 (fun i => A i ^ 2) - m ^ 2 := by
    have hsum : ∑ i, (A i - m) ^ 2 * boltzmannWeight beta E A 0 i
        = (∑ i, A i ^ 2 * boltzmannWeight beta E A 0 i)
          - 2 * m * (∑ i, A i * boltzmannWeight beta E A 0 i)
          + m ^ 2 * ∑ i, boltzmannWeight beta E A 0 i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hmm : m * partition beta E A 0 = ∑ i, A i * boltzmannWeight beta E A 0 i := by
      rw [hm, expect, div_mul_cancel₀ _ hZ]
    simp only [expect, hsum]
    rw [show (∑ i, boltzmannWeight beta E A 0 i) = partition beta E A 0 from rfl]
    field_simp
    rw [← hmm]; ring
  rw [key]
  exact fluctuation_dissipation beta E A

/-- The equilibrium expectation of a nonnegative observable is nonnegative. -/
lemma expect_nonneg [Nonempty ι] (beta : ℝ) (E A : ι → ℝ) (lam : ℝ) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) : 0 ≤ expect beta E A lam f :=
  div_nonneg
    (Finset.sum_nonneg fun i _ => mul_nonneg (hf i) (boltzmannWeight_pos beta E A lam i).le)
    (partition_pos beta E A lam).le

/-- Positivity of the static susceptibility: at nonnegative inverse temperature the
linear response of `A` to its own conjugate field is nonnegative, since by the
fluctuation-dissipation theorem it equals `β` times a variance. -/
theorem susceptibility_nonneg [Nonempty ι] {beta : ℝ} (hbeta : 0 ≤ beta) (E A : ι → ℝ) :
    0 ≤ deriv (fun lam => expect beta E A lam A) 0 := by
  rw [(fluctuation_dissipation_variance beta E A).deriv]
  exact mul_nonneg hbeta
    (expect_nonneg beta E A 0 _ fun i => sq_nonneg (A i - expect beta E A 0 A))

end Phys

