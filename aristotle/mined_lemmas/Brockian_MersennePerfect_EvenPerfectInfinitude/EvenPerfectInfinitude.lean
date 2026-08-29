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
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace MersennePerfect

/-- The set of even perfect natural numbers. -/

theorem EvenPerfectInfinitude :
    evenPerfects.Infinite ↔ mersenneExponents.Infinite := by
  constructor
  · intro h
    by_contra hfin
    rw [Set.not_infinite] at hfin
    exact h ((hfin.image _).subset evenPerfects_subset_image)
  · intro h
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨p, hp, hpN⟩ := h.exists_gt (N + 1)
    have h1 : 2 ^ (p - 1) * mersenne p ∈ evenPerfects :=
      mem_evenPerfects_of_mem_mersenneExponents hp
    have h2 : N < 2 ^ (p - 1) * mersenne p := by
      have hm : 1 ≤ mersenne p := by
        have hpp : (mersenne p).Prime := hp
        exact hpp.one_lt.le.trans' (by norm_num)
      calc N < 2 ^ N := Nat.lt_two_pow_self
        _ ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 2 ^ (p - 1) * mersenne p := Nat.le_mul_of_pos_right _ hm
    exact absurd (hN h1) (by omega)

/-- Non-vacuity check: `6` is an even perfect number. -/
example : (6 : ℕ) ∈ evenPerfects := ⟨by decide, by unfold Nat.Perfect; decide⟩

/-- Non-vacuity check: `28` is an even perfect number. -/
example : (28 : ℕ) ∈ evenPerfects := ⟨by decide, by unfold Nat.Perfect; decide⟩

/-- Non-vacuity check: `3` is a Mersenne prime exponent (`2 ^ 3 - 1 = 7`). -/
example : 3 ∈ mersenneExponents := by
  show (mersenne 3).Prime
  norm_num [mersenne]

end MersennePerfect
end Brockian

