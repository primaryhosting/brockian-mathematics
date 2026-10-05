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

/-
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Filter Topology MeasureTheory Complex

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian.Equidistribution

/-! ## Weyl averages of continuous functions on the circle -/

/-- The `N`-th Weyl average of a continuous function `f` on the circle `ℝ / ℤ`, sampled along the
orbit `n ↦ n • α` of the rotation by `α`. -/

theorem count_partition (α : ℝ) {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    countIco α 0 a N + countIco α a b N + countIco α b 1 N = N := by
  classical
  unfold countIco
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine (Finset.sum_eq_card_nsmul (b := (1 : ℕ)) fun n _ => ?_).trans (by simp)
  have h0 := Int.fract_nonneg ((n : ℝ) * α)
  have h1 := Int.fract_lt_one ((n : ℝ) * α)
  rcases lt_or_ge (Int.fract ((n : ℝ) * α)) a with hA | hA
  · rw [if_pos ⟨h0, hA⟩, if_neg (by push_neg; intro h; linarith),
      if_neg (by push_neg; intro h; linarith)]
  · rcases lt_or_ge (Int.fract ((n : ℝ) * α)) b with hB | hB
    · rw [if_neg (by push_neg; intro _; linarith), if_pos ⟨hA, hB⟩,
        if_neg (by push_neg; intro h; linarith)]
    · rw [if_neg (by push_neg; intro _; linarith), if_neg (by push_neg; intro _; linarith),
        if_pos ⟨hB, h1⟩]

/-- Lower bound: asymptotically, the orbit visits `[a, b)` at least a `(b - a) - ε` fraction of
the time. -/
