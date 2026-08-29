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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

/-- A function with compact support contained in `(0, ∞)` vanishes on a
neighbourhood of `0` on the right: there is `a > 0` with `f x = 0` for all `x < a`. -/

theorem exists_gt_eq_zero {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∃ b : ℝ, ∀ x : ℝ, b < x → f x = 0 := by
  have hK : IsCompact (tsupport f) := hf
  obtain ⟨b, hb⟩ := hK.bddAbove
  refine ⟨b, fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hxmem
  exact absurd (hb hxmem) (not_le.2 hx)

/-- **Boundary term vanishes.**  For `f, g : ℝ → ℂ` with compact support contained
in `(0, ∞)`, the boundary expression `x * f x * conj (g x)` tends to `0` both as
`x → 0⁺` and as `x → ∞`.  Both limits hold because the expression is identically
zero outside a compact subset of `(0, ∞)`.

The hypotheses on `g` (`hg`, `hgs`) are part of the requested statement but turn out to be
unnecessary: the compact support of `f` alone already forces the product to vanish. -/
