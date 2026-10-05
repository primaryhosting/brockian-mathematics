/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset Real

/-- The Bekenstein bound `2 π k R E / (ℏ c)` on the entropy of a system of energy `E`
contained in a sphere of radius `R`. -/
noncomputable def bekensteinBound (k hbar c R E : ℝ) : ℝ :=
  2 * Real.pi * k * R * E / (hbar * c)

/-- The Gibbs entropy `S = -k ∑ pᵢ log pᵢ` of a statistical state `p`. -/
noncomputable def gibbsEntropy {ι : Type*} [Fintype ι] (k : ℝ) (p : ι → ℝ) : ℝ :=
  -k * ∑ i, p i * Real.log (p i)

/-- The mean energy `∑ pᵢ Eᵢ` of a statistical state `p` with energy levels `E`. -/
def meanEnergy {ι : Type*} [Fintype ι] (p E : ι → ℝ) : ℝ := ∑ i, p i * E i

/-- Elementary form of Gibbs' inequality: `p log (q/p) ≤ q - p`. -/
lemma mul_log_sub_log_le_sub {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p * (Real.log q - Real.log p) ≤ q - p := by
  rcases eq_or_lt_of_le hp with h | hp'
  · simp [← h, hq.le]
  · have hlog : Real.log q - Real.log p = Real.log (q / p) := (Real.log_div hq.ne' hp'.ne').symm
    have h1 : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (div_pos hq hp')
    have h2 : p * Real.log (q / p) ≤ p * (q / p - 1) :=
      mul_le_mul_of_nonneg_left h1 hp'.le
    have h3 : p * (q / p - 1) = q - p := by field_simp
    rw [hlog]
    linarith

/-- Key statistical step: if the "partition function" at inverse temperature `β` is at most
one, then the Shannon entropy of any state is bounded by `β` times its mean energy. -/
lemma entropy_le_beta_mul_meanEnergy {ι : Type*} [Fintype ι] (beta : ℝ) (p E : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hZ : ∑ i, Real.exp (-(beta * E i)) ≤ 1) :
    -∑ i, p i * Real.log (p i) ≤ beta * ∑ i, p i * E i := by
  have key : ∀ i : ι, p i * (-(beta * E i) - Real.log (p i))
      ≤ Real.exp (-(beta * E i)) - p i := by
    intro i
    have h := mul_log_sub_log_le_sub (hp i) (Real.exp_pos (-(beta * E i)))
    rwa [Real.log_exp] at h
  have hsum' : ∑ i, p i * (-(beta * E i) - Real.log (p i))
      ≤ ∑ i, (Real.exp (-(beta * E i)) - p i) := Finset.sum_le_sum fun i _ => key i
  rw [Finset.sum_sub_distrib, hsum] at hsum'
  have hexp : ∑ i, p i * (-(beta * E i) - Real.log (p i))
      = -(beta * ∑ i, p i * E i) - ∑ i, p i * Real.log (p i) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hexp] at hsum'
  linarith

/-- **Bekenstein bound.**  For a quantum system confined to a sphere of radius `R`, whose
energy spectrum `E` satisfies the (modular-Hamiltonian) normalization
`∑ᵢ exp (-2πR Eᵢ / (ℏ c)) ≤ 1`, the Gibbs entropy of any state `p` of the system is bounded
by `2 π k R ⟨E⟩ / (ℏ c)`. -/
theorem bekenstein_bound {ι : Type*} [Fintype ι] (k hbar c R : ℝ) (p E : ι → ℝ)
    (hk : 0 < k) (hhbar : 0 < hbar) (hc : 0 < c)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hZ : ∑ i, Real.exp (-(2 * Real.pi * R / (hbar * c) * E i)) ≤ 1) :
    gibbsEntropy k p ≤ bekensteinBound k hbar c R (meanEnergy p E) := by
  have h := entropy_le_beta_mul_meanEnergy (2 * Real.pi * R / (hbar * c)) p E hp hsum hZ
  have hmul : k * (-∑ i, p i * Real.log (p i))
      ≤ k * ((2 * Real.pi * R / (hbar * c)) * ∑ i, p i * E i) :=
    mul_le_mul_of_nonneg_left h hk.le
  have hne : hbar * c ≠ 0 := (mul_pos hhbar hc).ne'
  unfold gibbsEntropy bekensteinBound meanEnergy
  rw [div_eq_mul_inv]
  have : 2 * Real.pi * k * R * (∑ i, p i * E i) * (hbar * c)⁻¹
      = k * ((2 * Real.pi * R / (hbar * c)) * ∑ i, p i * E i) := by
    field_simp
  rw [this]
  linarith

end Phys

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

