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

/-- If `f` has its closed support inside `(0, ∞)`, then `f` vanishes on a
neighbourhood of `0`. -/
lemma eventually_eq_zero_nhds_zero {f : ℝ → ℂ} (hf0 : tsupport f ⊆ Set.Ioi 0) :
    ∀ᶠ x in nhds (0 : ℝ), f x = 0 := by
  have hmem : (tsupport f)ᶜ ∈ nhds (0 : ℝ) := by
    refine (isClosed_tsupport f).isOpen_compl.mem_nhds ?_
    intro hcon
    exact lt_irrefl (0 : ℝ) (hf0 hcon)
  filter_upwards [hmem] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- A compactly supported function vanishes eventually at `+∞`. -/
lemma eventually_eq_zero_atTop {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∀ᶠ x in Filter.atTop, f x = 0 := by
  obtain ⟨R, hR⟩ := IsCompact.bddAbove hf
  filter_upwards [Filter.eventually_gt_atTop R] with x hx
  refine image_eq_zero_of_notMem_tsupport ?_
  intro hmem
  exact absurd (hR hmem) (not_le.mpr hx)

/-- **Boundary term vanishes.**  For `f`, `g` with compact support contained in
`(0, ∞)`, the boundary expression `x • f x • conj (g x)` tends to `0` both as
`x → 0⁺` and as `x → +∞`.  (Only the closed-support condition is needed at `0`;
compactness of the support is what gives the limit at `+∞`.  The hypotheses on
`g` are kept as requested, but turn out not to be needed: the factor `f x`
already vanishes near both boundary points.) -/
theorem boundary_term_vanishes (f g : ℝ → ℂ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hf0 : tsupport f ⊆ Set.Ioi 0) (hg0 : tsupport g ⊆ Set.Ioi 0) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        Filter.atTop (nhds 0) := by
  constructor
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    have h : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), f x = 0 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_eq_zero_nhds_zero hf0)
    filter_upwards [h] with x hx
    simp [hx]
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_eq_zero_atTop hf] with x hx
    simp [hx]

end DilationGenerator
end Brockian

