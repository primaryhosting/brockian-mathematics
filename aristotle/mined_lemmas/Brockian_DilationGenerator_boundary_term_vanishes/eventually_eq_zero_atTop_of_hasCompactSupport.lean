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
