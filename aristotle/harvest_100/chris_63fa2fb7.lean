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

set_option grind.warning false

namespace Phys

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Boltzmann weight `e^{-β H(i)}` of the microstate `i`. -/
noncomputable def gibbsWeight (β : ℝ) (H : ι → ℝ) (i : ι) : ℝ := Real.exp (-β * H i)

/-- Canonical partition function `Z = ∑_i e^{-β H(i)}`. -/
noncomputable def partitionFn (β : ℝ) (H : ι → ℝ) : ℝ := ∑ i, gibbsWeight β H i

/-- Equilibrium (canonical ensemble) average of the observable `f`. -/
noncomputable def thermalAvg (β : ℝ) (H : ι → ℝ) (f : ι → ℝ) : ℝ :=
  (∑ i, f i * gibbsWeight β H i) / partitionFn β H

lemma partitionFn_pos (β : ℝ) (H : ι → ℝ) : 0 < partitionFn β H := by
  refine Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

lemma partitionFn_ne_zero (β : ℝ) (H : ι → ℝ) : partitionFn β H ≠ 0 :=
  ne_of_gt (partitionFn_pos β H)

omit [Fintype ι] [Nonempty ι] in
/-- Derivative in the coupling `l` of the Boltzmann weight for the perturbed
Hamiltonian `H - l B`, evaluated at `l = 0`. -/
lemma hasDerivAt_gibbsWeight (β : ℝ) (H B : ι → ℝ) (i : ι) :
    HasDerivAt (fun l : ℝ => gibbsWeight β (fun j => H j - l * B j) i)
      (β * B i * gibbsWeight β H i) 0 := by
  have h1 : HasDerivAt (fun l : ℝ => -β * (H i - l * B i)) (β * B i) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (B i)).const_sub (H i)).const_mul (-β)
    simpa using this
  have h2 := h1.exp
  simp only [gibbsWeight]
  simpa [mul_comm] using h2

omit [Nonempty ι] in
/-- Derivative of the perturbed partition function at zero coupling. -/
lemma hasDerivAt_partitionFn (β : ℝ) (H B : ι → ℝ) :
    HasDerivAt (fun l : ℝ => partitionFn β (fun j => H j - l * B j))
      (∑ i, β * B i * gibbsWeight β H i) 0 := by
  unfold partitionFn
  exact HasDerivAt.fun_sum (fun i _ => hasDerivAt_gibbsWeight β H B i)

omit [Nonempty ι] in
/-- Derivative of the (unnormalized) perturbed expectation value at zero coupling. -/
lemma hasDerivAt_num (β : ℝ) (H B A : ι → ℝ) :
    HasDerivAt (fun l : ℝ => ∑ i, A i * gibbsWeight β (fun j => H j - l * B j) i)
      (∑ i, A i * (β * B i * gibbsWeight β H i)) 0 :=
  HasDerivAt.fun_sum (fun i _ => ((hasDerivAt_gibbsWeight β H B i).const_mul (A i)))

/--
**Fluctuation–dissipation theorem** (static / classical Kubo form).

For a finite classical system in canonical equilibrium at inverse temperature `β`
with Hamiltonian `H`, perturbing the Hamiltonian by `-l·B` and measuring the
observable `A`, the linear response coefficient (the static susceptibility,
i.e. the derivative of the equilibrium average of `A` with respect to the
coupling `l` at `l = 0`) equals `β` times the equilibrium correlation
(covariance) of `A` and `B`:

`χ_{AB} = β (⟨A B⟩ - ⟨A⟩⟨B⟩)`.

Dissipation (the response to an external field) is thus determined by the
spontaneous equilibrium fluctuations.
-/
theorem fluctuation_dissipation (β : ℝ) (H B A : ι → ℝ) :
    deriv (fun l : ℝ => thermalAvg β (fun j => H j - l * B j) A) 0
      = β * (thermalAvg β H (fun i => A i * B i)
              - thermalAvg β H A * thermalAvg β H B) := by
  have hZ : partitionFn β H ≠ 0 := partitionFn_ne_zero β H
  have hZ0 : (fun l : ℝ => partitionFn β (fun j => H j - l * B j)) 0 ≠ 0 := by
    simpa using hZ
  have hd :
      HasDerivAt (fun l : ℝ => thermalAvg β (fun j => H j - l * B j) A)
        (((∑ i, A i * (β * B i * gibbsWeight β H i)) *
            (fun l : ℝ => partitionFn β (fun j => H j - l * B j)) 0
          - (fun l : ℝ => ∑ i, A i * gibbsWeight β (fun j => H j - l * B j) i) 0 *
            (∑ i, β * B i * gibbsWeight β H i))
          / ((fun l : ℝ => partitionFn β (fun j => H j - l * B j)) 0) ^ 2) 0 :=
    (hasDerivAt_num β H B A).div (hasDerivAt_partitionFn β H B) hZ0
  rw [hd.deriv]
  simp only [sub_zero, zero_mul, thermalAvg]
  have e1 : ∑ i, A i * (β * B i * gibbsWeight β H i)
      = β * ∑ i, (A i * B i) * gibbsWeight β H i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have e2 : ∑ i, β * B i * gibbsWeight β H i
      = β * ∑ i, B i * gibbsWeight β H i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e1, e2]
  field_simp

/-- Cauchy–Schwarz for the equilibrium average: `⟨A⟩² ≤ ⟨A²⟩`. -/
lemma sq_thermalAvg_le (β : ℝ) (H A : ι → ℝ) :
    thermalAvg β H A ^ 2 ≤ thermalAvg β H (fun i => A i ^ 2) := by
  have hZ : 0 < partitionFn β H := partitionFn_pos β H
  have hcs : (∑ i, A i * gibbsWeight β H i) ^ 2
      ≤ (∑ i, gibbsWeight β H i) * ∑ i, A i ^ 2 * gibbsWeight β H i := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (fun i _ => le_of_lt (Real.exp_pos _))
      (fun i _ => mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _)))
      (fun i _ => by simp only [gibbsWeight]; ring)
  rw [thermalAvg, thermalAvg, div_pow, div_le_div_iff₀ (by positivity) hZ]
  calc (∑ i, A i * gibbsWeight β H i) ^ 2 * partitionFn β H
      ≤ ((∑ i, gibbsWeight β H i) * ∑ i, A i ^ 2 * gibbsWeight β H i) * partitionFn β H :=
        mul_le_mul_of_nonneg_right hcs hZ.le
    _ = (∑ i, A i ^ 2 * gibbsWeight β H i) * partitionFn β H ^ 2 := by
        rw [partitionFn]; ring

/-- Self-response form of the fluctuation–dissipation theorem: the susceptibility of an
observable `A` to its own conjugate field is `β` times the equilibrium variance of `A`. -/
theorem fluctuation_dissipation_variance (β : ℝ) (H A : ι → ℝ) :
    deriv (fun l : ℝ => thermalAvg β (fun j => H j - l * A j) A) 0
      = β * (thermalAvg β H (fun i => A i ^ 2) - thermalAvg β H A ^ 2) := by
  have h := fluctuation_dissipation β H A A
  rw [h]
  simp only [sq]

/-- Positivity of the static susceptibility at positive temperature: an immediate
consequence of the fluctuation–dissipation theorem, since a variance is nonnegative. -/
theorem fluctuation_dissipation_nonneg (β : ℝ) (hβ : 0 ≤ β) (H A : ι → ℝ) :
    0 ≤ deriv (fun l : ℝ => thermalAvg β (fun j => H j - l * A j) A) 0 := by
  rw [fluctuation_dissipation_variance]
  exact mul_nonneg hβ (sub_nonneg.mpr (sq_thermalAvg_le β H A))

end Phys

