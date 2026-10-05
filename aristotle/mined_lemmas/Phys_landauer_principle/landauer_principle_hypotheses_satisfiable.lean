/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

set_option grind.warning false

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Erasing one bit of information dissipates at least `k T log 2` of heat.

The setting formalised here is the standard statistical-mechanical derivation:

* the memory is a two-state system (`Bool`), initially in the uniform state
  (one bit of information, entropy `log 2`);
* the heat bath is a finite system with energies `E`, initially in the Gibbs
  state at inverse temperature `beta = 1 / (k T)`;
* system and bath are initially uncorrelated;
* the joint system is isolated, so its Shannon entropy does not decrease
  (in particular this holds, with equality, for reversible microscopic
  dynamics, i.e. for a bijection of the joint state space);
* the process is an *erasure*: the final marginal state of the memory is a
  point mass.

Then the heat `Q` absorbed by the bath is at least `k T log 2`.

The proof uses: invariance of Shannon entropy under relabelling, additivity on
product distributions, subadditivity (both consequences of Gibbs' inequality)
and the maximum-entropy property of the Gibbs state.
-/

namespace Phys

open Finset

/-- A probability distribution on a finite type. -/
structure IsProbDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  sum_one : ∑ a, p a = 1

/-- Shannon entropy (in nats) of a distribution on a finite type. -/

theorem landauer_principle_hypotheses_satisfiable :
    ∃ (k T : ℝ) (E gam : Fin 4 → ℝ) (r0 r1 : Bool × Fin 4 → ℝ) (s₀ : Bool) (Q : ℝ),
      0 < k ∧ 0 < T ∧
      gam = gibbsState E (1 / (k * T)) ∧
      (∀ x, r0 x = (1 / 2 : ℝ) * gam x.2) ∧
      IsProbDist r1 ∧
      shannonEntropy r0 ≤ shannonEntropy r1 ∧
      (∀ s, marg1 r1 s = if s = s₀ then 1 else 0) ∧
      Q = ∑ b, (marg2 r1 b - gam b) * E b := by
  classical
  set gam : Fin 4 → ℝ := gibbsState witnessEnergy 1 with hgam_def
  set r1 : Bool × Fin 4 → ℝ := fun x => if x.1 = false then (1 / 4 : ℝ) else 0 with hr1_def
  -- basic estimates on `exp (-10)`
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hexp10 : (243 : ℝ) ≤ Real.exp 10 := by
    have h : Real.exp 10 = Real.exp 2 * (Real.exp 2 * (Real.exp 2 * (Real.exp 2 * Real.exp 2))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      norm_num
    have a2 : (9 : ℝ) ≤ Real.exp 2 * Real.exp 2 := by nlinarith
    have a3 : (27 : ℝ) ≤ Real.exp 2 * (Real.exp 2 * Real.exp 2) := by nlinarith
    have a4 : (81 : ℝ) ≤ Real.exp 2 * (Real.exp 2 * (Real.exp 2 * Real.exp 2)) := by nlinarith
    rw [h]
    nlinarith
  have heps : Real.exp (-10) ≤ 1 / 243 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hexp10
  have hepspos : 0 < Real.exp (-10) := Real.exp_pos _
  -- values of the witness energies
  have hE0 : witnessEnergy 0 = 0 := by simp [witnessEnergy]
  have hE1 : witnessEnergy 1 = 10 := by simp [witnessEnergy]
  have hE2 : witnessEnergy 2 = 10 := by simp [witnessEnergy]
  have hE3 : witnessEnergy 3 = 10 := by simp [witnessEnergy]
  -- the partition function of the witness bath
  have hZ : partitionFn witnessEnergy 1 = 1 + 3 * Real.exp (-10) := by
    rw [partitionFn, Fin.sum_univ_four, hE0, hE1, hE2, hE3]
    simp only [mul_zero, neg_zero, Real.exp_zero, one_mul]
    ring
  have hZ1 : (1 : ℝ) ≤ partitionFn witnessEnergy 1 := by rw [hZ]; linarith
  have hZpos : (0 : ℝ) < partitionFn witnessEnergy 1 := by linarith
  have hZinv : (partitionFn witnessEnergy 1)⁻¹ ≤ 1 := by
    have h1 : (partitionFn witnessEnergy 1)⁻¹ * partitionFn witnessEnergy 1 = 1 :=
      inv_mul_cancel₀ (ne_of_gt hZpos)
    nlinarith [inv_pos.mpr hZpos, hZ1, h1]
  -- mean energy of the bath in the Gibbs state
  have hmean : ∑ b, gam b * witnessEnergy b
      = 30 * Real.exp (-10) * (partitionFn witnessEnergy 1)⁻¹ := by
    simp only [hgam_def, gibbsState_eq, div_eq_mul_inv]
    rw [Fin.sum_univ_four, hE0, hE1, hE2, hE3]
    simp only [mul_zero, neg_zero, Real.exp_zero, one_mul]
    ring
  have hmean_le : ∑ b, gam b * witnessEnergy b ≤ 30 * Real.exp (-10) := by
    rw [hmean]
    nlinarith [hepspos, hZinv]
  have hlogZ : Real.log (partitionFn witnessEnergy 1) ≤ 3 * Real.exp (-10) := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < partitionFn witnessEnergy 1 by linarith)
    rw [hZ] at h ⊢
    linarith
  -- entropy of the Gibbs state is tiny
  have hHgam : shannonEntropy gam ≤ 33 * Real.exp (-10) := by
    rw [hgam_def, entropy_gibbsState]
    linarith [hmean_le, hlogZ]
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hHgam_le : shannonEntropy gam ≤ Real.log 2 := by
    have : 33 * Real.exp (-10) ≤ 33 * (1 / 243) := by linarith
    linarith
  -- entropy of the final joint state
  have hHr1 : shannonEntropy r1 = 2 * Real.log 2 := by
    have h4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
      rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ (2 : ℕ))⁻¹ by norm_num, Real.log_inv, Real.log_pow]
      push_cast
      ring
    rw [shannonEntropy, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [hr1_def, Fin.sum_univ_four]
    norm_num [h4]
    ring
  refine ⟨1, 1, witnessEnergy, gam, fun x => (1 / 2 : ℝ) * gam x.2, r1, false,
    ∑ b, (marg2 r1 b - gam b) * witnessEnergy b, one_pos, one_pos, by
      rw [hgam_def]; norm_num, fun x => rfl, ⟨?_, ?_⟩, ?_, ?_, rfl⟩
  · intro x
    rw [hr1_def]
    dsimp only
    split <;> norm_num
  · rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [hr1_def, Fin.sum_univ_four]
    norm_num
  · -- the second law holds (with room to spare) for this process
    have hprod : shannonEntropy (fun x : Bool × Fin 4 => (1 / 2 : ℝ) * gam x.2)
        = Real.log 2 + shannonEntropy gam := by
      have hpS : IsProbDist (fun _ : Bool => (1 : ℝ) / 2) := by
        refine ⟨fun _ => by norm_num, ?_⟩
        rw [Fintype.sum_bool]; norm_num
      have hgamP : IsProbDist gam := by rw [hgam_def]; exact gibbsState_isProbDist witnessEnergy 1
      have := shannonEntropy_prod (fun _ : Bool => (1 : ℝ) / 2) gam hpS hgamP
      rw [shannonEntropy_uniform_bool] at this
      exact this
    rw [hprod, hHr1]
    linarith
  · intro s
    cases s <;> simp [hr1_def, marg1]

end Phys

