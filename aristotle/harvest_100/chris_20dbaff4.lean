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

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`countingFunction S t` is the number of points of `S` that are `≤ t`
(with the convention `ncard = 0` for infinite sets). -/
noncomputable def countingFunction (S : Set ℝ) (t : ℝ) : ℕ := (S ∩ Set.Iic t).ncard

/-- A spectrum is *discrete* when only finitely many of its points lie below any level. -/
def DiscreteSpectrum (S : Set ℝ) : Prop := ∀ t : ℝ, (S ∩ Set.Iic t).Finite

/-- The spectrum `S` *matches the Weyl law* in dimension `d` with leading constant `C`:
`N(t) / t ^ (d / 2) → C` as `t → ∞`, where `C > 0` and `d ≥ 1`. -/
def WeylLawMatch (S : Set ℝ) (d : ℕ) (C : ℝ) : Prop :=
  0 < C ∧ 0 < d ∧
    Tendsto (fun t : ℝ => (countingFunction S t : ℝ) / t ^ ((d : ℝ) / 2)) atTop (𝓝 C)

/-- If a spectrum has a discrete counting function and matches the Weyl law
`N(t) ∼ C · t ^ (d/2)` with `C > 0` and `d ≥ 1`, then the counting function diverges,
`N(t) → ∞`, and consequently the spectrum is infinite.

The discreteness hypothesis is part of the statement as named in the target; the proof of
divergence uses only the Weyl asymptotics (discreteness is what makes the counting function
meaningful in the first place). -/
theorem counting_diverges_of_discrete_and_WeylLawMatch
    (S : Set ℝ) (d : ℕ) (C : ℝ)
    (_hdisc : DiscreteSpectrum S) (hweyl : WeylLawMatch S d C) :
    Tendsto (countingFunction S) atTop atTop ∧ S.Infinite := by
  obtain ⟨hC, hd, hlim⟩ := hweyl
  have hpow : Tendsto (fun t : ℝ => t ^ ((d : ℝ) / 2)) atTop atTop := by
    refine tendsto_rpow_atTop ?_
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hmul := hlim.pos_mul_atTop hC hpow
  have hreal : Tendsto (fun t : ℝ => (countingFunction S t : ℝ)) atTop atTop := by
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hne : t ^ ((d : ℝ) / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
    field_simp
  have hdiv : Tendsto (countingFunction S) atTop atTop := tendsto_natCast_atTop_iff.mp hreal
  refine ⟨hdiv, ?_⟩
  intro hfin
  obtain ⟨t, ht⟩ := (hdiv.eventually_ge_atTop (S.ncard + 1)).exists
  have hle : countingFunction S t ≤ S.ncard :=
    Set.ncard_le_ncard Set.inter_subset_left hfin
  omega

/-! ## Non-vacuity: the hypotheses are satisfiable -/

/-- The nonnegative integers, viewed inside `ℝ`, form a spectrum whose points below `t`
are exactly the casts of the naturals `≤ ⌊t⌋₊`. -/
lemma natRange_inter_Iic_subset (t : ℝ) :
    (Set.range ((↑) : ℕ → ℝ) ∩ Set.Iic t) ⊆ ((↑) : ℕ → ℝ) '' (Set.Iic ⌊t⌋₊) := by
  rintro x ⟨⟨n, rfl⟩, hn⟩
  refine ⟨n, ?_, rfl⟩
  have ht : 0 ≤ t := le_trans (Nat.cast_nonneg n) hn
  exact (Nat.le_floor_iff ht).mpr hn

lemma countingFunction_natRange (t : ℝ) (ht : 0 ≤ t) :
    countingFunction (Set.range ((↑) : ℕ → ℝ)) t = ⌊t⌋₊ + 1 := by
  have hset : (Set.range ((↑) : ℕ → ℝ) ∩ Set.Iic t) = ((↑) : ℕ → ℝ) '' (Set.Iic ⌊t⌋₊) := by
    refine Set.Subset.antisymm (natRange_inter_Iic_subset t) ?_
    rintro x ⟨n, hn, rfl⟩
    exact ⟨⟨n, rfl⟩, (Nat.le_floor_iff ht).mp hn⟩
  have hIic : (Set.Iic ⌊t⌋₊) = ((Finset.Iic ⌊t⌋₊ : Finset ℕ) : Set ℕ) := by simp
  rw [countingFunction, hset, Set.ncard_image_of_injective _ Nat.cast_injective, hIic,
    Set.ncard_coe_finset]
  simp

/-- The hypotheses of the main theorem are not vacuous: the spectrum `ℕ ⊆ ℝ` is discrete and
matches the Weyl law in dimension `2` with leading constant `1`. -/
theorem discrete_and_weylLawMatch_natRange :
    DiscreteSpectrum (Set.range ((↑) : ℕ → ℝ)) ∧
      WeylLawMatch (Set.range ((↑) : ℕ → ℝ)) 2 1 := by
  refine ⟨fun t => Set.Finite.subset ((Set.finite_Iic _).image _) (natRange_inter_Iic_subset t),
    one_pos, two_pos, ?_⟩
  have hfloor : Tendsto (fun t : ℝ => ((⌊t⌋₊ : ℝ) + 1) / t) atTop (𝓝 1) := by
    have hinv : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
    have h1 : Tendsto (fun t : ℝ => (t + 1) / t) atTop (𝓝 1) := by
      have heq : (fun t : ℝ => 1 + 1 / t) =ᶠ[atTop] fun t : ℝ => (t + 1) / t := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        field_simp
      refine Tendsto.congr' heq ?_
      simpa using (tendsto_const_nhds (X := ℝ) (α := ℝ) (x := (1 : ℝ)) (f := atTop)).add hinv
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds (X := ℝ) (α := ℝ) (x := (1 : ℝ)) (f := atTop)) h1 ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [le_div_iff₀ ht]
      have := Nat.lt_floor_add_one t
      linarith
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      gcongr
      exact Nat.floor_le ht.le
  refine Tendsto.congr' ?_ hfloor
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [countingFunction_natRange t ht.le]
  norm_num [Real.rpow_one]

end Brockian.Weyl.WeylLawTarget

