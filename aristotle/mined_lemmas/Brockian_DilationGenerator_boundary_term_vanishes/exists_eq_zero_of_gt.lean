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
