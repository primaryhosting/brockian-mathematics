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

set_option autoImplicit false

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S t` is the number of spectral points `≤ t`. -/
noncomputable def counting (S : Set ℝ) (t : ℝ) : ℕ := (S ∩ Set.Iic t).ncard

/-- Discreteness of the spectrum, in the form used by Weyl-law arguments:
every sublevel set of the spectrum is finite. -/
def DiscreteSpectrum (S : Set ℝ) : Prop := ∀ t : ℝ, (S ∩ Set.Iic t).Finite

/-- "RVM" (resolvent vanishing at infinity / no highest eigenvalue):
the spectrum is unbounded above. -/
def RVM (S : Set ℝ) : Prop := ∀ M : ℝ, ∃ x ∈ S, M < x

/-- An unbounded-above set of reals is infinite. -/
theorem infinite_of_rvm {S : Set ℝ} (h : RVM S) : S.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  obtain ⟨x, hxS, hx⟩ := h M
  exact absurd (hM hxS) (not_le.mpr hx)

/-- The counting function is monotone. -/
theorem counting_mono {S : Set ℝ} (hS : DiscreteSpectrum S) : Monotone (counting S) := by
  intro a b hab
  exact Set.ncard_le_ncard (inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr hab)) (hS b)

/-- Given a discrete spectrum, any finite subset of it is contained in some sublevel set. -/
theorem exists_bound_of_finite {S : Set ℝ} {T : Finset ℝ} (hT : (T : Set ℝ) ⊆ S) :
    ∃ t : ℝ, (T : Set ℝ) ⊆ S ∩ Set.Iic t := by
  rcases T.exists_le with ⟨t, ht⟩
  exact ⟨t, fun x hx => ⟨hT hx, ht x (by simpa using hx)⟩⟩

/-- **Weyl-law divergence.** If the spectrum is discrete (finite sublevel sets) and satisfies
the RVM condition (unbounded above), then the eigenvalue counting function diverges. -/
theorem counting_diverges_of_discrete_and_rvm {S : Set ℝ}
    (hdisc : DiscreteSpectrum S) (hrvm : RVM S) :
    Filter.Tendsto (counting S) Filter.atTop Filter.atTop := by
  refine tendsto_atTop_atTop.mpr fun b => ?_
  obtain ⟨T, hTS, hTcard⟩ := (infinite_of_rvm hrvm).exists_subset_card_eq b
  obtain ⟨t, ht⟩ := exists_bound_of_finite hTS
  refine ⟨t, fun a hat => ?_⟩
  calc b = (T : Set ℝ).ncard := by simp [hTcard]
    _ ≤ counting S a :=
        Set.ncard_le_ncard (ht.trans (inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr hat)))
          (hdisc a)


/-! ### Eigenvalue-sequence form and a concrete instance -/

/-- If an eigenvalue sequence `lam` tends to `+∞`, its range is a discrete spectrum. -/
theorem discreteSpectrum_range_of_tendsto {lam : ℕ → ℝ}
    (h : Filter.Tendsto lam Filter.atTop Filter.atTop) :
    DiscreteSpectrum (Set.range lam) := by
  intro t
  obtain ⟨N, hN⟩ := (h.eventually_gt_atTop t).exists_forall_of_atTop
  have hsub : Set.range lam ∩ Set.Iic t ⊆ lam '' (Set.Iio N) := by
    rintro x ⟨⟨n, rfl⟩, hx⟩
    exact ⟨n, by
      simpa using not_le.mp fun hn => absurd hx (not_le.mpr (hN n hn)), rfl⟩
  exact Set.Finite.subset ((Set.finite_Iio N).image lam) hsub

/-- If an eigenvalue sequence `lam` tends to `+∞`, its range satisfies the RVM condition. -/
theorem rvm_range_of_tendsto {lam : ℕ → ℝ}
    (h : Filter.Tendsto lam Filter.atTop Filter.atTop) : RVM (Set.range lam) := by
  intro M
  obtain ⟨N, hN⟩ := (h.eventually_gt_atTop M).exists
  exact ⟨lam N, ⟨N, rfl⟩, hN⟩

/-- Sequence form of the target: the counting function of an eigenvalue sequence diverging
to `+∞` itself diverges. -/
theorem counting_range_diverges_of_tendsto {lam : ℕ → ℝ}
    (h : Filter.Tendsto lam Filter.atTop Filter.atTop) :
    Filter.Tendsto (counting (Set.range lam)) Filter.atTop Filter.atTop :=
  counting_diverges_of_discrete_and_rvm (discreteSpectrum_range_of_tendsto h)
    (rvm_range_of_tendsto h)

/-- Non-vacuity: the model spectrum `{n^2 : n ∈ ℕ}` is discrete, satisfies RVM, and hence has
a diverging counting function. -/
theorem counting_sq_diverges :
    DiscreteSpectrum (Set.range fun n : ℕ => (n : ℝ) ^ 2) ∧
      RVM (Set.range fun n : ℕ => (n : ℝ) ^ 2) ∧
      Filter.Tendsto (counting (Set.range fun n : ℕ => (n : ℝ) ^ 2))
        Filter.atTop Filter.atTop := by
  have h : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 2) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun n : ℕ => ?_) tendsto_natCast_atTop_atTop
    have hn : (n : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_self_pow two_ne_zero n)
    simpa using hn
  exact ⟨discreteSpectrum_range_of_tendsto h, rvm_range_of_tendsto h,
    counting_range_diverges_of_tendsto h⟩

end Brockian.Weyl.WeylLawTarget

