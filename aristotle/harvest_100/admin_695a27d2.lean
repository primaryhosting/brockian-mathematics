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
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- reproduced verbatim as a module docstring immediately after the import.)

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

/-- Boltzmann weight of the microstate `i` at inverse temperature `β` for the perturbed
Hamiltonian `H_lam = E - lam • B`. -/
noncomputable def weight (β : ℝ) (E B : ι → ℝ) (lam : ℝ) (i : ι) : ℝ :=
  Real.exp (-β * E i + β * lam * B i)

/-- Canonical partition function of the perturbed system. -/
noncomputable def partition (β : ℝ) (E B : ι → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, weight β E B lam i

/-- Canonical (Gibbs) expectation value of the observable `A` in the perturbed system. -/
noncomputable def expect (β : ℝ) (E B : ι → ℝ) (lam : ℝ) (A : ι → ℝ) : ℝ :=
  (∑ i, A i * weight β E B lam i) / partition β E B lam

/-- Equilibrium covariance (the "fluctuation") of two observables `A` and `B`. -/
noncomputable def covariance (β : ℝ) (E B : ι → ℝ) (A : ι → ℝ) : ℝ :=
  expect β E B 0 (fun i => A i * B i) - expect β E B 0 A * expect β E B 0 B

omit [Fintype ι] in
lemma weight_pos (β : ℝ) (E B : ι → ℝ) (lam : ℝ) (i : ι) : 0 < weight β E B lam i :=
  Real.exp_pos _

lemma partition_pos [Nonempty ι] (β : ℝ) (E B : ι → ℝ) (lam : ℝ) :
    0 < partition β E B lam :=
  Finset.sum_pos (fun i _ => weight_pos β E B lam i) univ_nonempty

omit [Fintype ι] in
lemma hasDerivAt_weight (β : ℝ) (E B : ι → ℝ) (lam : ℝ) (i : ι) :
    HasDerivAt (fun l => weight β E B l i) (β * B i * weight β E B lam i) lam := by
  have h : HasDerivAt (fun l : ℝ => -β * E i + β * l * B i) (β * B i) lam := by
    simpa using ((hasDerivAt_id lam).const_mul β).mul_const (B i) |>.const_add (-β * E i)
  simpa [weight, mul_comm, mul_left_comm, mul_assoc] using h.exp

lemma hasDerivAt_weighted_sum (β : ℝ) (E B A : ι → ℝ) (lam : ℝ) :
    HasDerivAt (fun l => ∑ i, A i * weight β E B l i)
      (∑ i, A i * (β * B i) * weight β E B lam i) lam := by
  have h := HasDerivAt.sum (u := (univ : Finset ι))
    (fun i _ => (hasDerivAt_weight β E B lam i).const_mul (A i))
  have e1 : (∑ i ∈ (univ : Finset ι), fun l => A i * weight β E B l i)
      = fun l => ∑ i, A i * weight β E B l i := by
    funext l; simp
  have e2 : ∑ i ∈ (univ : Finset ι), A i * (β * B i * weight β E B lam i)
      = ∑ i, A i * (β * B i) * weight β E B lam i :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2] at h
  exact h

lemma hasDerivAt_partition (β : ℝ) (E B : ι → ℝ) (lam : ℝ) :
    HasDerivAt (fun l => partition β E B l) (∑ i, (β * B i) * weight β E B lam i) lam := by
  have h := hasDerivAt_weighted_sum β E B (fun _ => 1) lam
  simpa [partition] using h

/-- **Fluctuation–dissipation theorem** (static / Kubo form).

For a classical system in the canonical ensemble at inverse temperature `β` with energy
levels `E`, the linear response (susceptibility) of the equilibrium average of an
observable `A` to a perturbation `H ↦ E - lam • B` of the Hamiltonian is exactly
`β` times the equilibrium covariance of `A` and `B`:

`d⟨A⟩_lam / d lam |_{lam = 0} = β * (⟨A B⟩₀ - ⟨A⟩₀ ⟨B⟩₀)`.

Dissipation (the response function on the left) is thus determined by the spontaneous
equilibrium fluctuations (the correlation function on the right). -/
theorem fluctuation_dissipation [Nonempty ι] (β : ℝ) (E B A : ι → ℝ) :
    HasDerivAt (fun lam => expect β E B lam A) (β * covariance β E B A) 0 := by
  have hZ : partition β E B 0 ≠ 0 := (partition_pos β E B 0).ne'
  have hN := hasDerivAt_weighted_sum β E B A 0
  have hD := hasDerivAt_partition β E B 0
  have hdiv := hN.div hD hZ
  refine hdiv.congr_deriv ?_
  have h1 : ∑ i, A i * (β * B i) * weight β E B 0 i
      = β * ∑ i, (A i * B i) * weight β E B 0 i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, (β * B i) * weight β E B 0 i = β * ∑ i, B i * weight β E B 0 i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2]
  simp only [expect, covariance]
  field_simp

/-! ## Dynamical (Kubo) form in the standard relaxation model

For an overdamped harmonic oscillator (Ornstein–Uhlenbeck process) with stiffness `k`,
relaxation time `tau` and inverse temperature `beta`, the equilibrium autocorrelation is
`corr t = (1 / (beta * k)) * exp (-t / tau)` (so `corr 0 = k_B T / k`), while the response to a
step force switched on at time `0` is `resp t = (1 / k) * (1 - exp (-t / tau))`.
The dynamical fluctuation–dissipation theorem states that the response function
(the derivative of the step response) equals `-beta` times the derivative of the
autocorrelation function. -/

/-- Equilibrium autocorrelation function of the Ornstein–Uhlenbeck (overdamped oscillator)
model. -/
noncomputable def corr (beta k tau t : ℝ) : ℝ := (1 / (beta * k)) * Real.exp (-t / tau)

/-- Step response of the Ornstein–Uhlenbeck (overdamped oscillator) model. -/
noncomputable def resp (k tau t : ℝ) : ℝ := (1 / k) * (1 - Real.exp (-t / tau))

lemma hasDerivAt_corr (beta k tau t : ℝ) :
    HasDerivAt (corr beta k tau) (-(1 / (beta * k * tau)) * Real.exp (-t / tau)) t := by
  have h : HasDerivAt (fun s : ℝ => -s / tau) (-1 / tau) t := by
    simpa [neg_div] using ((hasDerivAt_id t).neg).div_const tau
  have := (h.exp).const_mul (1 / (beta * k))
  refine this.congr_deriv ?_
  field_simp

lemma hasDerivAt_resp (k tau t : ℝ) :
    HasDerivAt (resp k tau) ((1 / (k * tau)) * Real.exp (-t / tau)) t := by
  have h : HasDerivAt (fun s : ℝ => -s / tau) (-1 / tau) t := by
    simpa [neg_div] using ((hasDerivAt_id t).neg).div_const tau
  have := ((h.exp).const_sub 1).const_mul (1 / k)
  refine this.congr_deriv ?_
  field_simp

/-- **Dynamical fluctuation–dissipation theorem** for the Ornstein–Uhlenbeck model:
the response function `resp'` is `-beta` times the time derivative of the equilibrium
correlation function `corr`. -/
theorem fluctuation_dissipation_dynamical (beta k tau t : ℝ) (hbeta : beta ≠ 0) :
    HasDerivAt (resp k tau) (-beta * deriv (corr beta k tau) t) t := by
  have hc : deriv (corr beta k tau) t = -(1 / (beta * k * tau)) * Real.exp (-t / tau) :=
    (hasDerivAt_corr beta k tau t).deriv
  rw [hc]
  refine (hasDerivAt_resp k tau t).congr_deriv ?_
  rcases eq_or_ne k 0 with hk | hk
  · simp [hk]
  · rcases eq_or_ne tau 0 with ht | ht
    · simp [ht]
    · field_simp

end Phys

