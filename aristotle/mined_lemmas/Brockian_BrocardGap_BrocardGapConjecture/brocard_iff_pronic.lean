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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.BrocardGap

/-! ### Elementary facts about perfect squares -/

/-- If `k` lies strictly between two consecutive squares, it is not a square. -/

theorem brocard_iff_pronic (n : ℕ) (hn : 2 ≤ n) :
    (∃ m, n ! + 1 = m ^ 2) ↔ ∃ a : ℕ, n ! = 4 * (a * (a + 1)) := by
  constructor
  · rintro ⟨m, hm⟩
    have hev : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
    have hodd : ¬ 2 ∣ m := by
      rintro ⟨t, rfl⟩
      have h4 : 2 ∣ (2 * t) ^ 2 := ⟨2 * t * t, by ring⟩
      rw [← hm] at h4
      omega
    obtain ⟨a, rfl⟩ : ∃ a, m = 2 * a + 1 := ⟨m / 2, by omega⟩
    refine ⟨a, ?_⟩
    have hx : (2 * a + 1) ^ 2 = 4 * (a * (a + 1)) + 1 := by ring
    rw [hx] at hm
    exact Nat.add_right_cancel hm
  · rintro ⟨a, ha⟩
    exact ⟨2 * a + 1, by rw [ha]; ring⟩

end Brockian.BrocardGap

