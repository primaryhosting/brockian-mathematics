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

import Mathlib

/-!
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem exists_pos_sub_posSemidef (hω : ω.PosDef) :
    ∃ m : ℝ, 0 < m ∧ (ω - ((m : ℝ) : ℂ) • 1).PosSemidef := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with he | hne
  · refine ⟨1, one_pos, ?_⟩
    have hzero : (ω - ((1 : ℝ) : ℂ) • 1 : Mat n) = 0 := by
      ext i j
      exact (IsEmpty.false i).elim
    rw [hzero]
    exact Matrix.PosSemidef.zero
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty (eigV hω), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      exact fun i _ => eigV_pos hω i
    · set m : ℝ := Finset.univ.inf' Finset.univ_nonempty (eigV hω) with hm
      refine posSemidef_of_cj hω ?_
      have hEq : ω - ((m : ℝ) : ℂ) • 1 = ω + ((-m : ℝ) : ℂ) • 1 := by
        push_cast
        module
      rw [hEq, cj_shift hω (-m)]
      refine Matrix.PosSemidef.diagonal fun i => ?_
      show (0 : ℂ) ≤ ((eigV hω i + -m : ℝ) : ℂ)
      have hle : m ≤ eigV hω i := Finset.inf'_le _ (Finset.mem_univ i)
      have hnn : (0 : ℝ) ≤ eigV hω i + -m := by linarith
      exact_mod_cast hnn

/-- A uniform bound on the quadratic resolvent traces. -/
