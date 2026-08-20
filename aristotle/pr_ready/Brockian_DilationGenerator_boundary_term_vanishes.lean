/-!
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
Statement: For f, g smooth with compact support in (0,∞), the boundary term x·f(x)·conj(g(x)) tends to 0 as x→0⁺ and as x→∞ (immediate from compact support — the honest form of the 'vanishing boundary' crux).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

/-- If the closed support of `f : ℝ → ℂ` is contained in `(0, ∞)`, then `f` vanishes on a
neighbourhood of `0`. -/
theorem eventually_eq_zero_nhds_zero {f : ℝ → ℂ} (hf : tsupport f ⊆ Set.Ioi (0 : ℝ)) :
    ∀ᶠ x in nhds (0 : ℝ), f x = 0 := by
  have h0 : (0 : ℝ) ∉ tsupport f := fun h => by simpa using hf h
  have hmem : (tsupport f)ᶜ ∈ nhds (0 : ℝ) :=
    (isClosed_tsupport f).isOpen_compl.mem_nhds h0
  filter_upwards [hmem] with x hx using image_eq_zero_of_notMem_tsupport hx

/-- A compactly supported function vanishes eventually at `+∞`. -/
theorem eventually_eq_zero_atTop {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∀ᶠ x in Filter.atTop, f x = 0 := by
  obtain ⟨R, hR⟩ := hf.isCompact.bddAbove
  filter_upwards [Filter.eventually_gt_atTop R] with x hx
  refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
  exact absurd (hR hmem) (not_le.mpr hx)

/-- **Boundary term vanishes.** For `f, g : ℝ → ℂ` with compact support contained in `(0, ∞)`,
the boundary expression `x * f x * conj (g x)` tends to `0` both as `x → 0⁺` and as `x → +∞`.

The hypotheses `hg` and `hg0` on `g` are kept as part of the requested statement, even though the
proof only needs the corresponding hypotheses on `f`. -/
theorem boundary_term_vanishes {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hf0 : tsupport f ⊆ Set.Ioi (0 : ℝ)) (hg0 : tsupport g ⊆ Set.Ioi (0 : ℝ)) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        Filter.atTop (nhds 0) := by
  constructor
  · have h : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (x : ℂ) * f x * (starRingEnd ℂ) (g x) = 0 := by
      filter_upwards [nhdsWithin_le_nhds (eventually_eq_zero_nhds_zero hf0)] with x hx
      simp [hx]
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm h) tendsto_const_nhds
  · have h : ∀ᶠ x : ℝ in Filter.atTop, (x : ℂ) * f x * (starRingEnd ℂ) (g x) = 0 := by
      filter_upwards [eventually_eq_zero_atTop hf] with x hx
      simp [hx]
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm h) tendsto_const_nhds

end DilationGenerator
end Brockian

#print axioms Brockian.DilationGenerator.boundary_term_vanishes

