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
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Filter Topology

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

/-- The spectral counting function of a set `S ⊆ ℝ` of spectral points: the number of points
of `S` in the symmetric window `[-T, T]`.

(When `S ∩ [-T, T]` is infinite this is `0` by the junk-value convention of `Set.ncard`;
the discreteness hypothesis below rules that out.) -/
noncomputable def counting (S : Set ℝ) (T : ℝ) : ℕ := (S ∩ Set.Icc (-T) T).ncard

/-- The Riemann–von Mangoldt main term `(T/2π) log (T/2π) - T/2π`. -/
noncomputable def rvmMainTerm (T : ℝ) : ℝ :=
  (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi)

/-- A finite set of reals is contained in every window `[-T, T]` with `T` large. -/
lemma exists_window_of_finset (F : Finset ℝ) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ x ∈ F, x ∈ Set.Icc (-T) T := by
  obtain ⟨M, hM⟩ := Finset.exists_le (F.image (fun x => |x|))
  refine ⟨M, fun T hT x hx => ?_⟩
  have hxM : |x| ≤ M := hM _ (Finset.mem_image_of_mem _ hx)
  have hxT : |x| ≤ T := hxM.trans hT
  exact ⟨by linarith [neg_abs_le x], (le_abs_self x).trans hxT⟩

/-- **Main target.**  If the spectrum `S` is discrete (only finitely many spectral points in
each bounded symmetric window) and the Riemann–von Mangoldt input holds (there are infinitely
many spectral points), then the spectral counting function diverges to `+∞`. -/
theorem counting_diverges_of_discrete_and_rvm
    (S : Set ℝ)
    (hdiscrete : ∀ T : ℝ, (S ∩ Set.Icc (-T) T).Finite)
    (hrvm : S.Infinite) :
    Filter.Tendsto (fun T : ℝ => (counting S T : ℝ)) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨F, hFS, hFcard⟩ := hrvm.exists_subset_card_eq ⌈b⌉₊
  obtain ⟨T₀, hT₀⟩ := exists_window_of_finset F
  refine ⟨T₀, fun T hT => ?_⟩
  have hsub : (↑F : Set ℝ) ⊆ S ∩ Set.Icc (-T) T := by
    intro x hx
    exact ⟨hFS hx, hT₀ T hT x (by simpa using hx)⟩
  have hcard : ⌈b⌉₊ ≤ counting S T := by
    have h := Set.ncard_le_ncard hsub (hdiscrete T)
    rwa [Set.ncard_coe_finset, hFcard] at h
  calc b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    _ ≤ (counting S T : ℝ) := by exact_mod_cast hcard

/-- Sanity check (non-vacuity): the hypotheses of the main target are simultaneously
satisfiable, e.g. by the spectrum `ℤ ⊆ ℝ`. -/
example : Filter.Tendsto (fun T : ℝ => (counting (Set.range (fun n : ℤ => (n : ℝ))) T : ℝ))
    Filter.atTop Filter.atTop := by
  refine counting_diverges_of_discrete_and_rvm _ (fun T => ?_) ?_
  · refine ((Set.finite_Icc (⌈-T⌉) (⌊T⌋)).image (fun n : ℤ => (n : ℝ))).subset ?_
    rintro x ⟨⟨n, rfl⟩, hx⟩
    exact ⟨n, by
      simp only [Set.mem_Icc]
      exact ⟨Int.ceil_le.2 (by exact_mod_cast hx.1), Int.le_floor.2 (by exact_mod_cast hx.2)⟩, rfl⟩
  · exact Set.infinite_range_of_injective (fun a b h => by exact_mod_cast h)

/-- The Riemann–von Mangoldt main term diverges to `+∞`. -/
theorem rvmMainTerm_tendsto_atTop :
    Filter.Tendsto rvmMainTerm Filter.atTop Filter.atTop := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hu : Filter.Tendsto (fun T : ℝ => T / (2 * Real.pi)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 fun b => ⟨b * (2 * Real.pi), fun T hT => by
      rw [le_div_iff₀ hpi]; exact hT⟩
  have hlog : Filter.Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi)) - 1)
      Filter.atTop Filter.atTop := by
    have h := Filter.tendsto_atTop_add_const_right _ (-1) (Real.tendsto_log_atTop.comp hu)
    simpa [Function.comp_apply, sub_eq_add_neg] using h
  exact (hu.atTop_mul_atTop₀ hlog).congr fun T => by simp only [rvmMainTerm]; ring

/-- If the counting function of a spectrum obeys the Riemann–von Mangoldt asymptotic
`N(T) ~ (T/2π) log (T/2π) - T/2π`, then it diverges to `+∞`. -/
theorem counting_diverges_of_rvm_asymptotic
    (S : Set ℝ)
    (hrvm : Filter.Tendsto (fun T : ℝ => (counting S T : ℝ) / rvmMainTerm T)
      Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun T : ℝ => (counting S T : ℝ)) Filter.atTop Filter.atTop := by
  have hmain := rvmMainTerm_tendsto_atTop
  have hprod := hrvm.pos_mul_atTop one_pos hmain
  refine hprod.congr' ?_
  have hne : ∀ᶠ T : ℝ in Filter.atTop, rvmMainTerm T ≠ 0 := by
    filter_upwards [hmain.eventually_gt_atTop 0] with T hT using ne_of_gt hT
  filter_upwards [hne] with T hT
  field_simp

end Brockian.Weyl.WeylLawTarget

