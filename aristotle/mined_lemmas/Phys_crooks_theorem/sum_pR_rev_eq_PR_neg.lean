/-
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- A microscopic setup for the Crooks fluctuation theorem.

`Γ` is a (finite) space of microscopic trajectories of the driven system.
`rev` is time reversal on trajectories, `W` is the work performed along a trajectory
(which changes sign under time reversal), `pF` and `pR` are the probability weights of
trajectories in the forward and in the reverse protocol, `beta` is the inverse temperature
and `dF` the free energy difference between the two equilibrium end states.

The physical input is `microscopic_reversibility`, the detailed-balance relation
`p_F(γ) = e^{β (W(γ) - ΔF)} · p_R(γ̄)`. -/
structure CrooksSetup (Γ : Type*) [Fintype Γ] where
  /-- Time reversal of trajectories. -/
  rev : Γ → Γ
  /-- Time reversal is an involution. -/
  rev_involutive : Function.Involutive rev
  /-- Work performed along a trajectory. -/
  W : Γ → ℝ
  /-- Work is odd under time reversal. -/
  W_rev : ∀ γ, W (rev γ) = -W γ
  /-- Probability weight of a trajectory in the forward protocol. -/
  pF : Γ → ℝ
  /-- Probability weight of a trajectory in the reverse protocol. -/
  pR : Γ → ℝ
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Free energy difference. -/
  dF : ℝ
  /-- Microscopic reversibility (detailed balance). -/
  microscopic_reversibility :
    ∀ γ, pF γ = Real.exp (beta * (W γ - dF)) * pR (rev γ)

variable {Γ : Type*} [Fintype Γ] (S : CrooksSetup Γ)

/-- The forward work distribution `P_F(w)`: total forward probability of trajectories
performing work exactly `w`. -/

theorem sum_pR_rev_eq_PR_neg (w : ℝ) :
    ∑ γ ∈ Finset.univ.filter (fun γ => S.W γ = w), S.pR (S.rev γ) = S.PR (-w) := by
  classical
  unfold CrooksSetup.PR
  refine Finset.sum_nbij' (i := fun γ => S.rev γ) (j := fun δ => S.rev δ) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [S.W_rev, ha]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [S.W_rev, ha, neg_neg]
  · intro a _
    exact S.rev_involutive a
  · intro a _
    exact S.rev_involutive a
  · intro a _
    rfl

/-- **Crooks fluctuation theorem.**

For every value `w` of the work, the forward and reverse work distributions satisfy
`P_F(w) = e^{β (w - ΔF)} · P_R(-w)`, and consequently, whenever `P_R(-w) ≠ 0`,
`P_F(w) / P_R(-w) = e^{β (w - ΔF)}`. -/
