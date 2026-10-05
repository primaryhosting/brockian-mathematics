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

/-!
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BrocardGap

open Nat

/-- `n` is a *Brocard number* if `n ! + 1` is a perfect square.
The known Brocard numbers are `4`, `5` and `7` (Brown numbers `(4,5)`, `(5,11)`, `(7,71)`). -/

theorem isBrocard_iff_pronic (n : ℕ) (hn : 2 ≤ n) :
    IsBrocard n ↔ ∃ u : ℕ, n ! = 4 * u * (u + 1) := by
  have hfac : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
  constructor
  · rintro ⟨m, hm⟩
    have hodd : Odd (m ^ 2) := by
      rw [← hm]
      exact Even.add_one ((even_iff_two_dvd).2 hfac)
    have hm' : Odd m := Nat.Odd.of_mul_right hodd
    obtain ⟨u, hu⟩ := hm'
    refine ⟨u, ?_⟩
    have h2 : n ! + 1 = 4 * u * (u + 1) + 1 := by rw [hm, hu]; ring
    exact Nat.add_right_cancel h2
  · rintro ⟨u, hu⟩
    exact ⟨2 * u + 1, by rw [hu]; ring⟩

/-- **Unconditional verification of the initial range.** For every `n ≤ 50`, the number `n ! + 1`
is a perfect square exactly when `n ∈ {4, 5, 7}`. -/
