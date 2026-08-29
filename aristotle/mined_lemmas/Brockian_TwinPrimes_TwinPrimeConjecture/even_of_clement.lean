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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.TwinPrimes

open Nat

/-- `p` is a twin prime (the smaller member of a twin prime pair) if both `p` and `p + 2`
are prime. -/

private lemma even_of_clement {k : ℕ}
    (h : (k + 3) * (k + 5) ∣ 4 * ((k + 2)! + 1) + (k + 3)) : ∃ j, k = 2 * j := by
  refine ⟨k / 2, ?_⟩
  by_contra hodd
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
  have hB := dvd_two_mul_of_clement h
  have hB' : (j + 3) ∣ 2 * (2 * j + 1 + 2)! + 1 := by
    have : (2 : ℕ) * (j + 3) ∣ 2 * (2 * (2 * j + 1 + 2)! + 1) := by
      simpa [show 2 * j + 1 + 5 = 2 * (j + 3) by ring] using hB
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp this
  have hfac : (j + 3) ∣ (2 * j + 1 + 2)! :=
    Nat.dvd_factorial (by omega) (by omega)
  have : (j + 3) ∣ 1 := (Nat.dvd_add_iff_right (hfac.mul_left 2)).mpr hB'
  have := Nat.le_of_dvd one_pos this
  omega

/-- **Clement's criterion** (backward direction): if `n ≥ 3` and
`n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`, then `n` and `n + 2` are both prime. -/
