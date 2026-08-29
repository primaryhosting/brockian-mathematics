/-
# Boundary Term Vanishes

Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` to precede any module docstring `/-! ... -/`, so the header
above is a plain block comment and is repeated as a module docstring below.)
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

/-- If a function has compact support contained in `(0, ∞)`, then it vanishes on a
neighbourhood of `0`. -/
theorem eventually_eq_zero_nhds_zero_of_tsupport_subset_Ioi
    {f : ℝ → ℂ} (hf0 : tsupport f ⊆ Set.Ioi (0 : ℝ)) :
    ∀ᶠ x : ℝ in nhds 0, f x = 0 := by
  have hclosed : IsClosed (tsupport f) := isClosed_tsupport f
  have hmem : (tsupport f)ᶜ ∈ nhds (0 : ℝ) := by
    refine hclosed.isOpen_compl.mem_nhds ?_
    intro h
    exact absurd (hf0 h) (by simp)
  filter_upwards [hmem] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- A function with compact support vanishes eventually at `+∞`. -/
theorem eventually_eq_zero_atTop_of_hasCompactSupport
    {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∀ᶠ x : ℝ in Filter.atTop, f x = 0 := by
  obtain ⟨b, hb⟩ := hf.isCompact.bddAbove
  filter_upwards [Filter.eventually_gt_atTop b] with x hx
  refine image_eq_zero_of_notMem_tsupport ?_
  intro hmem
  exact absurd (hb hmem) (not_le.2 hx)

/-- **Boundary term vanishes.**

For `f, g : ℝ → ℂ` with compact support contained in `(0, ∞)` (as for smooth compactly
supported functions on the half-line), the boundary expression `x * f x * conj (g x)`
tends to `0` both as `x → 0⁺` and as `x → +∞`.

Route: outside a compact subset of `(0, ∞)` the product is identically `0`, so the
function is eventually equal to the constant `0` along each of the two filters.
The first limit only needs `tsupport ⊆ (0, ∞)` (as `tsupport` is closed and `0 ∉ (0,∞)`);
the second uses that a compact support is bounded above. -/
theorem boundary_term_vanishes
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hf0 : tsupport f ⊆ Set.Ioi (0 : ℝ)) (hg0 : tsupport g ⊆ Set.Ioi (0 : ℝ)) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
      Filter.atTop (nhds 0) := by
  constructor
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    have h : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), f x = 0 :=
      (eventually_eq_zero_nhds_zero_of_tsupport_subset_Ioi hf0).filter_mono
        nhdsWithin_le_nhds
    have h' : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), g x = 0 :=
      (eventually_eq_zero_nhds_zero_of_tsupport_subset_Ioi hg0).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [h, h'] with x hx hx'
    simp [hx, hx']
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_eq_zero_atTop_of_hasCompactSupport hf,
      eventually_eq_zero_atTop_of_hasCompactSupport hg] with x hx hx'
    simp [hx, hx']

end DilationGenerator
end Brockian

