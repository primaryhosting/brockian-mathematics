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

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

/-- A function with compact support contained in `(0, ∞)` vanishes on a whole
neighbourhood `(-∞, ε)` of the origin, for some `ε > 0`. -/
theorem exists_pos_eq_zero_of_lt {f : ℝ → ℂ} (hf : HasCompactSupport f)
    (hf0 : tsupport f ⊆ Set.Ioi 0) : ∃ ε > 0, ∀ x < ε, f x = 0 := by
  rcases Set.eq_empty_or_nonempty (tsupport f) with h | h
  · refine ⟨1, one_pos, fun x _ => image_eq_zero_of_notMem_tsupport ?_⟩
    rw [h]
    exact Set.notMem_empty x
  · have hmem : sInf (tsupport f) ∈ tsupport f := hf.sInf_mem h
    have hpos : 0 < sInf (tsupport f) := hf0 hmem
    refine ⟨sInf (tsupport f), hpos, fun x hx => image_eq_zero_of_notMem_tsupport ?_⟩
    intro hxmem
    exact absurd (csInf_le hf.isCompact.bddBelow hxmem) (not_le.mpr hx)

/-- A function with compact support vanishes outside a bounded region. -/
theorem exists_eq_zero_of_gt {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∃ M : ℝ, ∀ x > M, f x = 0 := by
  obtain ⟨M, hM⟩ := hf.isCompact.bddAbove
  refine ⟨M, fun x hx => image_eq_zero_of_notMem_tsupport fun hxmem => ?_⟩
  exact absurd (hM hxmem) (not_le.mpr hx)

/-- **Boundary term vanishes.**  For `f g : ℝ → ℂ` with compact support contained in
`(0, ∞)`, the boundary expression `x * f x * conj (g x)` tends to `0` both as
`x → 0⁺` and as `x → ∞`.  Both limits are immediate from the support condition:
outside a compact subset of `(0, ∞)` the expression is identically zero.

The hypotheses on `g` are kept, as stated in the problem, even though the support
conditions on `f` alone already force the expression to vanish near `0` and near `∞`. -/
theorem boundary_term_vanishes {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hf0 : tsupport f ⊆ Set.Ioi 0) (hg0 : tsupport g ⊆ Set.Ioi 0) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) ∧
      Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        Filter.atTop (nhds 0) := by
  obtain ⟨ε, hε, hfε⟩ := exists_pos_eq_zero_of_lt hf hf0
  obtain ⟨M, hfM⟩ := exists_eq_zero_of_gt hf
  constructor
  · have hev : (fun _ : ℝ => (0 : ℂ)) =ᶠ[nhdsWithin 0 (Set.Ioi (0 : ℝ))]
        fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x) := by
      have h0 : {x : ℝ | x < ε} ∈ nhds (0 : ℝ) := gt_mem_nhds hε
      filter_upwards [nhdsWithin_le_nhds h0] with x hx
      simp [hfε x hx]
    exact Filter.Tendsto.congr' hev tendsto_const_nhds
  · have hev : (fun _ : ℝ => (0 : ℂ)) =ᶠ[Filter.atTop]
        fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x) := by
      filter_upwards [Filter.eventually_gt_atTop M] with x hx
      simp [hfM x hx]
    exact Filter.Tendsto.congr' hev tendsto_const_nhds

end DilationGenerator
end Brockian

