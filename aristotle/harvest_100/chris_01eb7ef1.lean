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

namespace Brockian.DilationGenerator

/-- If `f` has compact support contained in `(0, ∞)`, then `f` vanishes on a whole
neighbourhood of `0` in `ℝ`. -/
theorem eventually_eq_zero_nhds_zero_of_tsupport_subset_Ioi
    {f : ℝ → ℂ} (hf0 : tsupport f ⊆ Set.Ioi 0) :
    ∀ᶠ x : ℝ in nhds 0, f x = 0 := by
  have hmem : (tsupport f)ᶜ ∈ nhds (0 : ℝ) :=
    (isClosed_tsupport f).isOpen_compl.mem_nhds (fun h => by simpa using hf0 h)
  filter_upwards [hmem] with x hx using image_eq_zero_of_notMem_tsupport hx

/-- If `f` has compact support, then `f` vanishes eventually along `atTop`. -/
theorem eventually_eq_zero_atTop_of_hasCompactSupport
    {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∀ᶠ x : ℝ in Filter.atTop, f x = 0 := by
  have hc : IsCompact (tsupport f) := hf
  obtain ⟨b, hb⟩ := hc.bddAbove
  filter_upwards [Filter.eventually_gt_atTop b] with x hx
  refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
  exact absurd (hb hmem) (not_le.mpr hx)

/-- **Boundary term vanishes.**  For `f, g : ℝ → ℂ` with compact support contained in
`(0, ∞)`, the boundary expression `x * f x * conj (g x)` tends to `0` both as `x → 0⁺`
and as `x → ∞`.

(The hypotheses on `g` are stated as requested, although the argument only needs those
on `f`.) -/
theorem boundary_term_vanishes
    (f g : ℝ → ℂ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hf0 : tsupport f ⊆ Set.Ioi 0) (hg0 : tsupport g ⊆ Set.Ioi 0) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
    ∧ Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        Filter.atTop (nhds 0) := by
  clear hg hg0
  constructor
  · refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℂ)))
    filter_upwards [nhdsWithin_le_nhds
      (eventually_eq_zero_nhds_zero_of_tsupport_subset_Ioi hf0)] with x hx
    simp [hx]
  · refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℂ)))
    filter_upwards [eventually_eq_zero_atTop_of_hasCompactSupport hf] with x hx
    simp [hx]

end Brockian.DilationGenerator

