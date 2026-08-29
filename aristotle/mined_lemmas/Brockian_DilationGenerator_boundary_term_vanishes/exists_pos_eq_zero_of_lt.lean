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

theorem exists_pos_eq_zero_of_lt {f : ℝ → ℂ} (hf : HasCompactSupport f)
    (hsupp : tsupport f ⊆ Set.Ioi (0 : ℝ)) :
    ∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, x < a → f x = 0 := by
  rcases Set.eq_empty_or_nonempty (tsupport f) with h | h
  · refine ⟨1, one_pos, fun x _ => ?_⟩
    apply image_eq_zero_of_notMem_tsupport
    rw [h]
    exact Set.notMem_empty x
  · have hK : IsCompact (tsupport f) := hf
    have hmem : sInf (tsupport f) ∈ tsupport f := hK.sInf_mem h
    have hpos : 0 < sInf (tsupport f) := hsupp hmem
    refine ⟨sInf (tsupport f), hpos, fun x hx => ?_⟩
    apply image_eq_zero_of_notMem_tsupport
    intro hxmem
    exact absurd (csInf_le hK.bddBelow hxmem) (not_le.2 hx)

/-- A function with compact support vanishes far out to the right: there is `b`
with `f x = 0` for all `x > b`. -/
