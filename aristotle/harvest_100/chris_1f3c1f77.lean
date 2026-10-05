/-
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

/-- If the closed support of `f` lies in `(0, ∞)`, then `f` vanishes on a
punctured right neighbourhood of `0`. -/
theorem eventually_eq_zero_nhdsWithin_zero
    {f : ℝ → ℂ} (hf : tsupport f ⊆ Set.Ioi (0 : ℝ)) :
    ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), f x = 0 := by
  have h0 : (0 : ℝ) ∉ tsupport f := fun h => by simpa using hf h
  have hmem : (tsupport f)ᶜ ∈ nhds (0 : ℝ) :=
    (isClosed_tsupport f).isOpen_compl.mem_nhds h0
  filter_upwards [nhdsWithin_le_nhds hmem] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- A function with compact support vanishes eventually at `+∞`. -/
theorem eventually_eq_zero_atTop
    {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∀ᶠ x in Filter.atTop, f x = 0 := by
  obtain ⟨R, hR⟩ := hf.isCompact.bddAbove
  filter_upwards [Filter.eventually_gt_atTop R] with x hx
  exact image_eq_zero_of_notMem_tsupport (fun h => absurd (hR h) (not_le.2 hx))

/-- **Boundary term vanishes.**  For `f g : ℝ → ℂ` with compact support contained in
`(0, ∞)`, the boundary expression `x * f x * conj (g x)` tends to `0` both as
`x → 0⁺` and as `x → +∞`.

The hypotheses `hgc` (compact support of `g`) and `hg0` (support of `g` inside `(0, ∞)`)
are part of the requested statement; the proof only needs the corresponding hypotheses
on `f`, since `f` alone already vanishes near `0⁺` and near `+∞`. -/
theorem boundary_term_vanishes
    {f g : ℝ → ℂ} (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf0 : tsupport f ⊆ Set.Ioi (0 : ℝ)) (hg0 : tsupport g ⊆ Set.Ioi (0 : ℝ)) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        Filter.atTop (nhds 0) := by
  constructor
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_eq_zero_nhdsWithin_zero hf0] with x hx
    simp [hx]
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_eq_zero_atTop hfc] with x hx
    simp [hx]

/-- The literal reading of the informal statement: for `f, g : ℝ → ℂ` **smooth** with compact
support contained in `(0, ∞)`, the boundary term `x * f x * conj (g x)` tends to `0` both as
`x → 0⁺` and as `x → +∞`.  Smoothness is not needed for the conclusion; it is recorded here
because it is part of the informal hypotheses. -/
theorem boundary_term_vanishes_of_smooth
    {f g : ℝ → ℂ} (hfs : ContDiff ℝ (⊤ : ℕ∞) f) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf0 : tsupport f ⊆ Set.Ioi (0 : ℝ)) (hg0 : tsupport g ⊆ Set.Ioi (0 : ℝ)) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        Filter.atTop (nhds 0) :=
  boundary_term_vanishes hfc hgc hf0 hg0

end DilationGenerator
end Brockian

#print axioms Brockian.DilationGenerator.boundary_term_vanishes
#print axioms Brockian.DilationGenerator.boundary_term_vanishes_of_smooth

