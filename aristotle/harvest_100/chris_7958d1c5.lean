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

/-- A function with compact support contained in `(0, ∞)` vanishes outside a compact
interval `[a, b]` with `a > 0`. -/
theorem exists_vanishing_outside_of_hasCompactSupport
    (f : ℝ → ℂ) (hf : HasCompactSupport f) (hsupp : tsupport f ⊆ Set.Ioi (0 : ℝ)) :
    ∃ a b : ℝ, 0 < a ∧ ∀ x : ℝ, (x < a ∨ b < x) → f x = 0 := by
  have hzero : ∀ x : ℝ, x ∉ tsupport f → f x = 0 := fun x hx => by
    by_contra h
    exact hx (subset_tsupport f h)
  rcases Set.eq_empty_or_nonempty (tsupport f) with hempty | hne
  · refine ⟨1, 0, one_pos, fun x _ => hzero x ?_⟩
    rw [hempty]
    exact Set.notMem_empty x
  · obtain ⟨p, hp, hpmin⟩ := hf.exists_isMinOn hne continuousOn_id
    obtain ⟨q, hq, hqmax⟩ := hf.exists_isMaxOn hne continuousOn_id
    refine ⟨p, q, hsupp hp, fun x hx => hzero x ?_⟩
    intro hmem
    rcases hx with hx | hx
    · exact absurd (hpmin hmem) (not_le.mpr hx)
    · exact absurd (hqmax hmem) (not_le.mpr hx)

/-- **Vanishing boundary term.**

For `f, g : ℝ → ℂ` with compact support contained in `(0, ∞)`, the boundary expression
`x * f x * conj (g x)` tends to `0` both as `x → 0⁺` and as `x → ∞`.

(The hypotheses on `g` are stated as requested; the argument only needs those on `f`,
since the product vanishes wherever `f` does.) -/
theorem boundary_term_vanishes
    (f g : ℝ → ℂ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : tsupport f ⊆ Set.Ioi (0 : ℝ)) (hgs : tsupport g ⊆ Set.Ioi (0 : ℝ)) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        Filter.atTop (nhds 0) := by
  obtain ⟨a, b, ha, hab⟩ := exists_vanishing_outside_of_hasCompactSupport f hf hfs
  constructor
  · have hev : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (x : ℂ) * f x * (starRingEnd ℂ) (g x) = 0 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds ha)] with x hx
      simp [hab x (Or.inl hx)]
    exact Filter.Tendsto.congr' (hev.mono fun x hx => hx.symm) tendsto_const_nhds
  · have hev : ∀ᶠ x : ℝ in Filter.atTop,
        (x : ℂ) * f x * (starRingEnd ℂ) (g x) = 0 := by
      filter_upwards [Filter.eventually_gt_atTop b] with x hx
      simp [hab x (Or.inr hx)]
    exact Filter.Tendsto.congr' (hev.mono fun x hx => hx.symm) tendsto_const_nhds

end DilationGenerator
end Brockian

