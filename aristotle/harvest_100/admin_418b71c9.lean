/-
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian
namespace DilationGenerator

open Filter Set Topology

/-- If `f` has compact support contained in `(0, ∞)`, then `f` vanishes on a whole
neighbourhood of `0`. -/
theorem eventually_eq_zero_nhds_zero {f : ℝ → ℂ} (hf0 : tsupport f ⊆ Set.Ioi 0) :
    ∀ᶠ x : ℝ in nhds (0 : ℝ), f x = 0 := by
  have hclosed : IsClosed (tsupport f) := isClosed_tsupport f
  have h0 : (0 : ℝ) ∉ tsupport f := fun h => by simpa using hf0 h
  have hmem : (tsupport f)ᶜ ∈ nhds (0 : ℝ) := hclosed.isOpen_compl.mem_nhds h0
  filter_upwards [hmem] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- If `f` has compact support then `f` vanishes for all sufficiently large arguments. -/
theorem eventually_eq_zero_atTop {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∀ᶠ x : ℝ in Filter.atTop, f x = 0 := by
  obtain ⟨R, hR⟩ := (hf.isCompact.bddAbove)
  filter_upwards [Filter.eventually_gt_atTop R] with x hx
  refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
  exact absurd (hR hmem) (not_le.mpr hx)

/-- **Boundary term vanishes.** For `f, g : ℝ → ℂ` with compact support contained in
`(0, ∞)`, the boundary expression `x * f x * conj (g x)` tends to `0` both as `x → 0⁺`
and as `x → ∞`.

The hypotheses `hg` (compact support of `g`) and `hg0` (support of `g` inside `(0, ∞)`)
are kept because they are part of the requested statement, even though the compact-support
conditions on `f` alone already force both limits. -/
theorem boundary_term_vanishes {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hf0 : tsupport f ⊆ Set.Ioi 0) (hg0 : tsupport g ⊆ Set.Ioi 0) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        Filter.atTop (nhds 0) := by
  constructor
  · have h : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (x : ℂ) * f x * (starRingEnd ℂ) (g x) = 0 := by
      filter_upwards [nhdsWithin_le_nhds (eventually_eq_zero_nhds_zero hf0)] with x hx
      simp [hx]
    exact tendsto_const_nhds.congr' (h.mono fun x hx => hx.symm)
  · have h : ∀ᶠ x : ℝ in Filter.atTop,
        (x : ℂ) * f x * (starRingEnd ℂ) (g x) = 0 := by
      filter_upwards [eventually_eq_zero_atTop hf] with x hx
      simp [hx]
    exact tendsto_const_nhds.congr' (h.mono fun x hx => hx.symm)

end DilationGenerator
end Brockian

