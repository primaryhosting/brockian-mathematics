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


theorem pos_path {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : s ∈ uIcc (0:ℝ) 1) :
    0 < q + s * (p - q) := by
  rw [Set.uIcc_of_le (by norm_num)] at hs
  obtain ⟨h0, h1⟩ := hs
  have heq : q + s * (p - q) = (1 - s) * q + s * p := by ring
  rw [heq]
  rcases eq_or_lt_of_le h1 with h | h
  · subst h; simp; linarith
  · have : 0 < (1 - s) * q := by nlinarith
    nlinarith

