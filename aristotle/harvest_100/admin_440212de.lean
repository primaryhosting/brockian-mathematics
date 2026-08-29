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
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open Filter Topology

namespace Brockian.Weyl.WeylLawTarget

/-- A set of eigenvalues `S ⊆ ℝ` is a *discrete spectrum* when only finitely many of its
elements lie below any given threshold. -/
def DiscreteSpectrum (S : Set ℝ) : Prop :=
  ∀ lam : ℝ, (S ∩ Set.Iic lam).Finite

/-- The eigenvalue counting function `N(λ) = #{ x ∈ S : x ≤ λ }`. -/
noncomputable def counting (S : Set ℝ) (lam : ℝ) : ℕ :=
  (S ∩ Set.Iic lam).ncard

/-- `S` *matches a Weyl law* with constant `C` in dimension `d` when
`N(λ) / λ ^ (d / 2) → C` as `λ → ∞`, with `C > 0` and `d > 0`. -/
def WeylLawMatch (S : Set ℝ) (C d : ℝ) : Prop :=
  0 < C ∧ 0 < d ∧
    Tendsto (fun lam : ℝ => (counting S lam : ℝ) / lam ^ (d / 2)) atTop (𝓝 C)

theorem counting_diverges_of_discrete_and_WeylLawMatch
    {S : Set ℝ} {C d : ℝ} (hdisc : DiscreteSpectrum S) (hW : WeylLawMatch S C d) :
    Tendsto (fun lam : ℝ => (counting S lam : ℝ)) atTop atTop ∧
      ∀ M : ℝ, ∃ x ∈ S, M < x := by
  obtain ⟨hC, hd, hlim⟩ := hW
  have hpow : Tendsto (fun lam : ℝ => lam ^ (d / 2)) atTop atTop :=
    Real.tendsto_rpow_atTop (by positivity)
  have hmul : Tendsto
      (fun lam : ℝ => ((counting S lam : ℝ) / lam ^ (d / 2)) * lam ^ (d / 2)) atTop atTop :=
    hlim.pos_mul_atTop hC hpow
  have hdiv : Tendsto (fun lam : ℝ => (counting S lam : ℝ)) atTop atTop := by
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    have : lam ^ (d / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlam _)
    field_simp
  refine ⟨hdiv, ?_⟩
  intro M
  by_contra hcon
  push_neg at hcon
  have hSsub : S ⊆ Set.Iic M := fun x hx => hcon x hx
  have hSfin : S.Finite := by
    have := hdisc M
    rwa [Set.inter_eq_self_of_subset_left hSsub] at this
  have hbound : ∀ lam : ℝ, (counting S lam : ℝ) ≤ (S.ncard : ℝ) := by
    intro lam
    exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left hSfin
  obtain ⟨lam, hlam⟩ := (hdiv.eventually_ge_atTop ((S.ncard : ℝ) + 1)).exists
  linarith [hbound lam]

end Brockian.Weyl.WeylLawTarget

