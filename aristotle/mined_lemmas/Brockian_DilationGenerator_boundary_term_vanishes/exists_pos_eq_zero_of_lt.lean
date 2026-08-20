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
