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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S Λ` is the number of spectral points `≤ Λ`. -/
noncomputable def counting (S : Set ℝ) (Λ : ℝ) : ℕ := (S ∩ Set.Iic Λ).ncard

/-- A spectrum is *discrete* when only finitely many spectral points lie below any threshold. -/
def DiscreteSpectrum (S : Set ℝ) : Prop := ∀ Λ : ℝ, (S ∩ Set.Iic Λ).Finite

/-- Weyl-law matching with constant `C` in dimension `d`:
`counting S Λ / Λ ^ (d / 2) → C` as `Λ → ∞`. -/
def WeylLawMatch (S : Set ℝ) (C d : ℝ) : Prop :=
  Tendsto (fun Λ : ℝ => (counting S Λ : ℝ) / Λ ^ (d / 2)) atTop (nhds C)

/-- **Target.** If a spectrum `S` is discrete and obeys a Weyl law with positive Weyl constant
`C` in positive dimension `d`, then its counting function diverges to `+∞`.

The proof writes `counting S Λ = (counting S Λ / Λ ^ (d/2)) * Λ ^ (d/2)` for `Λ > 0`, where the
first factor tends to `C > 0` and the second to `+∞`.

The discreteness hypothesis is part of the requested statement; it is kept even though the
asymptotic hypothesis alone already forces the divergence. -/
theorem counting_diverges_of_discrete_and_WeylLawMatch
    (S : Set ℝ) (C d : ℝ) (hC : 0 < C) (hd : 0 < d)
    (_hdisc : DiscreteSpectrum S) (hW : WeylLawMatch S C d) :
    Tendsto (fun Λ : ℝ => (counting S Λ : ℝ)) atTop atTop := by
  have hpow : Tendsto (fun Λ : ℝ => Λ ^ (d / 2)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  have hmul :
      Tendsto (fun Λ : ℝ => ((counting S Λ : ℝ) / Λ ^ (d / 2)) * Λ ^ (d / 2)) atTop atTop :=
    hW.pos_mul_atTop hC hpow
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  have : Λ ^ (d / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hΛ _)
  field_simp

/-! ### Non-vacuity: a concrete spectrum satisfying all hypotheses -/

/-- The model spectrum `{0, 1, 2, …} ⊆ ℝ`. -/
def natSpectrum : Set ℝ := Set.range (fun n : ℕ => (n : ℝ))

theorem natSpectrum_inter_Iic (Λ : ℝ) :
    natSpectrum ∩ Set.Iic Λ ⊆ (fun n : ℕ => (n : ℝ)) '' (Set.Iic ⌊Λ⌋₊) := by
  rintro x ⟨⟨n, rfl⟩, hx⟩
  exact ⟨n, Nat.le_floor hx, rfl⟩

theorem discreteSpectrum_natSpectrum : DiscreteSpectrum natSpectrum := fun Λ =>
  Set.Finite.subset ((Set.finite_Iic ⌊Λ⌋₊).image _) (natSpectrum_inter_Iic Λ)

theorem counting_natSpectrum (Λ : ℝ) (hΛ : 0 ≤ Λ) : counting natSpectrum Λ = ⌊Λ⌋₊ + 1 := by
  have hset : natSpectrum ∩ Set.Iic Λ = (fun n : ℕ => (n : ℝ)) '' (Set.Iic ⌊Λ⌋₊) := by
    refine Set.Subset.antisymm (natSpectrum_inter_Iic Λ) ?_
    rintro x ⟨n, hn, rfl⟩
    exact ⟨⟨n, rfl⟩, le_trans (by exact_mod_cast Nat.cast_le.mpr hn) (Nat.floor_le hΛ)⟩
  rw [counting, hset, Set.ncard_image_of_injective _ (fun a b h => by exact_mod_cast h),
    ← Finset.coe_Iic, Set.ncard_coe_finset, Nat.card_Iic]

theorem weylLawMatch_natSpectrum : WeylLawMatch natSpectrum 1 2 := by
  have h1 : Tendsto (fun Λ : ℝ => 1 + 1 / Λ) atTop (nhds 1) := by
    have h := tendsto_inv_atTop_zero (𝕜 := ℝ)
    simpa [one_div] using tendsto_const_nhds.add h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_ <;>
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
  · have h0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
    rw [counting_natSpectrum Λ h0.le, show ((2 : ℝ) / 2) = 1 by norm_num, Real.rpow_one,
      le_div_iff₀ h0]
    have := (Nat.lt_floor_add_one Λ).le
    push_cast
    linarith
  · have h0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
    rw [counting_natSpectrum Λ h0.le, show ((2 : ℝ) / 2) = 1 by norm_num, Real.rpow_one,
      div_le_iff₀ h0]
    have hinv : (1 : ℝ) / Λ * Λ = 1 := by field_simp
    push_cast
    nlinarith [Nat.floor_le h0.le, h0]

/-- The hypotheses of the target theorem are satisfiable, so the statement is not vacuous. -/
theorem counting_natSpectrum_diverges :
    Tendsto (fun Λ : ℝ => (counting natSpectrum Λ : ℝ)) atTop atTop :=
  counting_diverges_of_discrete_and_WeylLawMatch natSpectrum 1 2 one_pos two_pos
    discreteSpectrum_natSpectrum weylLawMatch_natSpectrum

end Brockian.Weyl.WeylLawTarget

