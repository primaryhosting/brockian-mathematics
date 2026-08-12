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

open Filter Topology Set

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S Λ` is the number of points of `S` that are `≤ Λ`. -/
noncomputable def counting (S : Set ℝ) (Λ : ℝ) : ℕ := (S ∩ Set.Iic Λ).ncard

/-- `S` has *discrete spectrum* if only finitely many spectral points lie below
any given threshold. -/
def DiscreteSpectrum (S : Set ℝ) : Prop := ∀ Λ : ℝ, (S ∩ Set.Iic Λ).Finite

/-- `S` *matches a Weyl law* with constant `C > 0` and dimension exponent `d > 0`
if its counting function is asymptotic to `C * Λ ^ (d / 2)` as `Λ → ∞`. -/
def WeylLawMatch (S : Set ℝ) (C d : ℝ) : Prop :=
  0 < C ∧ 0 < d ∧
    Tendsto (fun Λ : ℝ => (counting S Λ : ℝ) / (C * Λ ^ (d / 2))) atTop (𝓝 1)

/-- If the counting function is eventually bounded below by a function tending to
`atTop`, then it tends to `atTop`. -/
theorem counting_tendsto_atTop_of_eventually_le
    (S : Set ℝ) (g : ℝ → ℝ) (hg : Tendsto g atTop atTop)
    (h : ∀ᶠ Λ : ℝ in atTop, g Λ ≤ (counting S Λ : ℝ)) :
    Tendsto (fun Λ : ℝ => counting S Λ) atTop atTop := by
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  exact tendsto_atTop_mono' atTop h hg

/-- A Weyl-law match forces the counting function to eventually dominate
`(C / 2) * Λ ^ (d / 2)`. -/
theorem eventually_half_le_counting_of_WeylLawMatch
    {S : Set ℝ} {C d : ℝ} (hW : WeylLawMatch S C d) :
    ∀ᶠ Λ : ℝ in atTop, (C / 2) * Λ ^ (d / 2) ≤ (counting S Λ : ℝ) := by
  obtain ⟨hC, hd, hlim⟩ := hW
  have h1 : ∀ᶠ Λ : ℝ in atTop,
      (1 : ℝ) / 2 < (counting S Λ : ℝ) / (C * Λ ^ (d / 2)) := by
    have : Set.Ioi ((1 : ℝ) / 2) ∈ 𝓝 (1 : ℝ) :=
      Ioi_mem_nhds (by norm_num)
    exact hlim this
  filter_upwards [h1, eventually_gt_atTop (0 : ℝ)] with Λ hΛ hΛ0
  have hpow : (0 : ℝ) < Λ ^ (d / 2) := Real.rpow_pos_of_pos hΛ0 _
  have hden : (0 : ℝ) < C * Λ ^ (d / 2) := mul_pos hC hpow
  rw [lt_div_iff₀ hden] at hΛ
  nlinarith [hΛ, hpow, hC]

/-- The dominating function `(C / 2) * Λ ^ (d / 2)` tends to infinity. -/
theorem tendsto_half_rpow_atTop {C d : ℝ} (hC : 0 < C) (hd : 0 < d) :
    Tendsto (fun Λ : ℝ => (C / 2) * Λ ^ (d / 2)) atTop atTop :=
  Tendsto.const_mul_atTop (by positivity) (tendsto_rpow_atTop (by linarith))

/--
**Counting diverges, given a discrete spectrum matching a Weyl law.**

If `S ⊆ ℝ` is a discrete spectrum whose counting function satisfies a Weyl law
`counting S Λ ∼ C * Λ ^ (d / 2)` with `C > 0` and `d > 0`, then
the counting function is monotone, diverges to infinity, and `S` is infinite.
-/
theorem counting_diverges_of_discrete_and_WeylLawMatch
    {S : Set ℝ} {C d : ℝ} (hdisc : DiscreteSpectrum S) (hW : WeylLawMatch S C d) :
    Monotone (fun Λ : ℝ => counting S Λ) ∧
      Tendsto (fun Λ : ℝ => counting S Λ) atTop atTop ∧ S.Infinite := by
  obtain ⟨hC, hd, -⟩ := id hW
  have hmono : Monotone (fun Λ : ℝ => counting S Λ) := by
    intro Λ₁ Λ₂ h
    exact Set.ncard_le_ncard
      (Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr h)) (hdisc Λ₂)
  have hdiv : Tendsto (fun Λ : ℝ => counting S Λ) atTop atTop :=
    counting_tendsto_atTop_of_eventually_le S _
      (tendsto_half_rpow_atTop hC hd)
      (eventually_half_le_counting_of_WeylLawMatch hW)
  refine ⟨hmono, hdiv, ?_⟩
  by_contra hfin
  rw [Set.not_infinite] at hfin
  -- a finite spectrum has a uniformly bounded counting function
  have hbdd : ∀ Λ : ℝ, counting S Λ ≤ S.ncard := by
    intro Λ
    exact Set.ncard_le_ncard Set.inter_subset_left hfin
  obtain ⟨Λ₀, hΛ₀⟩ := (hdiv.eventually_ge_atTop (S.ncard + 1)).exists
  exact absurd (hbdd Λ₀) (by omega)

/-! ## Non-vacuity: the hypotheses are simultaneously satisfiable

We exhibit an explicit spectrum, `natSpec = {0, 1, 2, ...} ⊆ ℝ`, which is discrete
and matches the Weyl law with `C = 1`, `d = 2`. -/

/-- The spectrum consisting of all natural numbers, viewed inside `ℝ`. -/
def natSpec : Set ℝ := Set.range (fun n : ℕ => (n : ℝ))

theorem natSpec_inter_Iic {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    natSpec ∩ Set.Iic Λ = (fun n : ℕ => (n : ℝ)) '' (Set.Iic ⌊Λ⌋₊) := by
  ext x
  simp only [natSpec, Set.mem_inter_iff, Set.mem_range, Set.mem_Iic, Set.mem_image]
  constructor
  · rintro ⟨⟨n, rfl⟩, hn⟩
    exact ⟨n, (Nat.le_floor_iff hΛ).mpr hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, rfl⟩, (Nat.le_floor_iff hΛ).mp hn⟩

theorem counting_natSpec {Λ : ℝ} (hΛ : 0 ≤ Λ) : counting natSpec Λ = ⌊Λ⌋₊ + 1 := by
  rw [counting, natSpec_inter_Iic hΛ, Set.ncard_image_of_injective _ Nat.cast_injective,
    ← Finset.coe_Iic, Set.ncard_coe_finset, Nat.card_Iic]

theorem discreteSpectrum_natSpec : DiscreteSpectrum natSpec := by
  intro Λ
  rcases le_or_gt 0 Λ with hΛ | hΛ
  · rw [natSpec_inter_Iic hΛ]
    exact (Set.finite_Iic _).image _
  · apply Set.Finite.subset Set.finite_empty
    rintro x ⟨⟨n, rfl⟩, hn⟩
    simp only [Set.mem_Iic] at hn
    exact absurd hn (by push_neg; linarith [Nat.cast_nonneg (α := ℝ) n])

theorem weylLawMatch_natSpec : WeylLawMatch natSpec 1 2 := by
  refine ⟨one_pos, two_pos, ?_⟩
  have key : Tendsto (fun Λ : ℝ => ((⌊Λ⌋₊ : ℝ) + 1) / Λ) atTop (𝓝 1) := by
    have hub : Tendsto (fun Λ : ℝ => 1 + 1 / Λ) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (X := ℝ) (α := ℝ) (x := (1 : ℝ)) (f := atTop)).add
        tendsto_inv_atTop_zero
      simpa [one_div] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
      rw [le_div_iff₀ hΛ, one_mul]
      linarith [Nat.lt_floor_add_one Λ]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
      rw [div_le_iff₀ hΛ]
      have : (⌊Λ⌋₊ : ℝ) ≤ Λ := Nat.floor_le hΛ.le
      field_simp
      nlinarith
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  rw [counting_natSpec hΛ.le]
  norm_num [Real.rpow_one]

/-- The hypotheses of the main theorem are satisfiable, so the conclusion is not
vacuous: `natSpec` is discrete, matches a Weyl law, and its counting function
indeed diverges. -/
theorem counting_natSpec_diverges :
    Monotone (fun Λ : ℝ => counting natSpec Λ) ∧
      Tendsto (fun Λ : ℝ => counting natSpec Λ) atTop atTop ∧ natSpec.Infinite :=
  counting_diverges_of_discrete_and_WeylLawMatch discreteSpectrum_natSpec
    weylLawMatch_natSpec

end Brockian.Weyl.WeylLawTarget

