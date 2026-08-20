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
