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

/-- The spectral counting function of a set `S ⊆ ℝ` (thought of as the spectrum of an
operator, listed without multiplicity): `spectralCounting S t` is the number of spectral
points that are `≤ t`. -/
noncomputable def spectralCounting (S : Set ℝ) (t : ℝ) : ℕ := (S ∩ Set.Iic t).ncard

/-- A spectrum `S ⊆ ℝ` is *discrete* when only finitely many spectral points lie below any
given threshold, i.e. the spectrum can accumulate only at `+∞`. -/
def IsDiscreteSpectrum (S : Set ℝ) : Prop := ∀ t : ℝ, (S ∩ Set.Iic t).Finite

/-- `WeylLawMatch S C d` says that the counting function of `S` matches the Weyl asymptotic
`N(t) ∼ C · t ^ (d / 2)` as `t → ∞`. -/
def WeylLawMatch (S : Set ℝ) (C d : ℝ) : Prop :=
  Tendsto (fun t : ℝ => (spectralCounting S t : ℝ) / (C * t ^ (d / 2))) atTop (𝓝 1)

/-- The counting function diverges as soon as it matches a Weyl asymptotic with positive
constant `C` and positive dimension `d`. -/
theorem counting_tendsto_atTop_of_WeylLawMatch {S : Set ℝ} {C d : ℝ} (hC : 0 < C) (hd : 0 < d)
    (hweyl : WeylLawMatch S C d) :
    Tendsto (fun t : ℝ => (spectralCounting S t : ℝ)) atTop atTop := by
  have hpow : Tendsto (fun t : ℝ => t ^ (d / 2)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  have hX : Tendsto (fun t : ℝ => C * t ^ (d / 2)) atTop atTop := hpow.const_mul_atTop hC
  have key :
      Tendsto (fun t : ℝ =>
        ((spectralCounting S t : ℝ) / (C * t ^ (d / 2))) * (C * t ^ (d / 2))) atTop atTop :=
    hweyl.pos_mul_atTop one_pos hX
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hne : C * t ^ (d / 2) ≠ 0 := by positivity
  field_simp

/-- If the counting function of `S` diverges, then `S` is infinite. -/
theorem infinite_of_counting_tendsto_atTop {S : Set ℝ}
    (h : Tendsto (fun t : ℝ => (spectralCounting S t : ℝ)) atTop atTop) : S.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have hbound : ∀ t : ℝ, (spectralCounting S t : ℝ) ≤ (S.ncard : ℝ) := by
    intro t
    exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left hfin
  obtain ⟨t, ht⟩ := (h.eventually_ge_atTop ((S.ncard : ℝ) + 1)).exists
  linarith [hbound t]

/--
**Weyl law forces a divergent, infinite, unbounded spectrum.**

If a spectrum `S ⊆ ℝ` is discrete (finitely many points below every threshold) and its
counting function matches the Weyl asymptotic `N(t) ∼ C · t ^ (d / 2)` with `C > 0` and
`d > 0`, then the counting function diverges to `+∞`, the spectrum is infinite, and it is
unbounded above.

The divergence and the infinitude already follow from the Weyl asymptotic alone; the
discreteness hypothesis named in the statement is what upgrades infinitude to
unboundedness above.
-/
theorem counting_diverges_of_discrete_and_WeylLawMatch {S : Set ℝ} {C d : ℝ}
    (hC : 0 < C) (hd : 0 < d) (hdisc : IsDiscreteSpectrum S) (hweyl : WeylLawMatch S C d) :
    Tendsto (fun t : ℝ => (spectralCounting S t : ℝ)) atTop atTop ∧ S.Infinite ∧ ¬ BddAbove S := by
  have hdiv := counting_tendsto_atTop_of_WeylLawMatch hC hd hweyl
  have hinf := infinite_of_counting_tendsto_atTop hdiv
  refine ⟨hdiv, hinf, ?_⟩
  rintro ⟨b, hb⟩
  have hsub : S ⊆ S ∩ Set.Iic b := fun x hx => ⟨hx, hb hx⟩
  exact hinf ((hdisc b).subset hsub)

/-! ### Non-vacuity: the hypotheses are satisfiable

The spectrum `S = {0, 1, 2, ...} ⊆ ℝ` is discrete and matches the Weyl asymptotic
`N(t) ∼ 1 · t ^ (2 / 2)`, so the hypotheses of the theorem above are not vacuous. -/

/-- The natural numbers, viewed as a spectrum inside `ℝ`. -/
def natSpectrum : Set ℝ := Set.range (fun n : ℕ => (n : ℝ))

theorem natSpectrum_inter_Iic (t : ℝ) :
    natSpectrum ∩ Set.Iic t ⊆ (fun n : ℕ => (n : ℝ)) '' Set.Iic ⌊t⌋₊ := by
  rintro x ⟨⟨n, rfl⟩, hx⟩
  have ht : (0 : ℝ) ≤ t := le_trans (Nat.cast_nonneg n) hx
  exact ⟨n, Nat.le_floor (by simpa using hx), rfl⟩

theorem spectralCounting_natSpectrum {t : ℝ} (ht : 0 ≤ t) :
    spectralCounting natSpectrum t = ⌊t⌋₊ + 1 := by
  have hset : natSpectrum ∩ Set.Iic t = (fun n : ℕ => (n : ℝ)) '' Set.Iic ⌊t⌋₊ := by
    refine Set.Subset.antisymm (natSpectrum_inter_Iic t) ?_
    rintro x ⟨n, hn, rfl⟩
    exact ⟨⟨n, rfl⟩, by
      simpa using (Nat.cast_le (α := ℝ) |>.mpr hn).trans (Nat.floor_le ht)⟩
  rw [spectralCounting, hset, Set.ncard_image_of_injective _ Nat.cast_injective,
    Set.ncard_Iic_nat]

theorem isDiscreteSpectrum_natSpectrum : IsDiscreteSpectrum natSpectrum := fun t =>
  Set.Finite.subset ((Set.finite_Iic ⌊t⌋₊).image _) (natSpectrum_inter_Iic t)

theorem weylLawMatch_natSpectrum : WeylLawMatch natSpectrum 1 2 := by
  have hlim : Tendsto (fun t : ℝ => ((⌊t⌋₊ : ℝ) + 1) / t) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℝ => 1 + 1 / t) atTop (𝓝 1) := by
      simpa [one_div] using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ))).add
        tendsto_inv_atTop_zero
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [le_div_iff₀ ht]
      linarith [Nat.lt_floor_add_one t]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hmul : (1 + 1 / t) * t = t + 1 := by field_simp
      rw [div_le_iff₀ ht, hmul]
      linarith [Nat.floor_le ht.le]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [spectralCounting_natSpectrum ht]
  norm_num

/-- The hypotheses of `counting_diverges_of_discrete_and_WeylLawMatch` are satisfiable. -/
theorem exists_discrete_spectrum_with_WeylLawMatch :
    ∃ (S : Set ℝ) (C d : ℝ), 0 < C ∧ 0 < d ∧ IsDiscreteSpectrum S ∧ WeylLawMatch S C d :=
  ⟨natSpectrum, 1, 2, one_pos, two_pos, isDiscreteSpectrum_natSpectrum, weylLawMatch_natSpectrum⟩

end Brockian.Weyl.WeylLawTarget

