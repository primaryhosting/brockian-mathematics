import Mathlib

/-!
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian
namespace DilationGenerator

/-- If `tsupport f ⊆ Set.Ioi 0`, then `f` vanishes on a neighbourhood of `0`. -/
theorem eventually_eq_zero_nhds_zero_of_tsupport_subset_Ioi
    {f : ℝ → ℂ} (hf : tsupport f ⊆ Set.Ioi 0) :
    ∀ᶠ x in nhds (0 : ℝ), f x = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  have hmem : (0 : ℝ) ∈ (tsupport f)ᶜ := by
    intro h
    exact absurd (hf h) (by simp)
  filter_upwards [hopen.mem_nhds hmem] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- A compactly supported function vanishes eventually along `atTop`. -/
theorem eventually_eq_zero_atTop_of_hasCompactSupport
    {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∀ᶠ x in Filter.atTop, f x = 0 := by
  obtain ⟨R, hR⟩ := hf.isCompact.bddAbove
  filter_upwards [Filter.eventually_gt_atTop R] with x hx
  refine image_eq_zero_of_notMem_tsupport ?_
  intro hmem
  exact absurd (hR hmem) (not_le.mpr hx)

/-- **Boundary term vanishes.**  For `f, g : ℝ → ℂ` with compact support contained in
`(0, ∞)`, the boundary expression `x * f x * conj (g x)` tends to `0` both as `x → 0⁺`
and as `x → ∞`.  Both limits hold because the expression is identically zero outside a
compact subset of `(0, ∞)`.

The hypotheses `hg` (compact support of `g`) and `hg0` (`tsupport g ⊆ (0, ∞)`) are kept as
requested, but turn out to be unnecessary: the vanishing of `f` alone already forces the
product to be zero near `0` and near `+∞`. -/
theorem boundary_term_vanishes
    {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hf0 : tsupport f ⊆ Set.Ioi 0) (hg0 : tsupport g ⊆ Set.Ioi 0) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        Filter.atTop (nhds 0) := by
  constructor
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [nhdsWithin_le_nhds
      (eventually_eq_zero_nhds_zero_of_tsupport_subset_Ioi hf0)] with x hx
    simp [hx]
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_eq_zero_atTop_of_hasCompactSupport hf] with x hx
    simp [hx]

end DilationGenerator
end Brockian

