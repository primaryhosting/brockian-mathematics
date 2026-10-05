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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of its divisors equals `2 * n + 1`,
i.e. the sum of its proper divisors is `n + 1`. -/

theorem QuasiperfectExists :
    (∃ n : ℕ, 0 < n ∧ Quasiperfect n) ↔ (∃ m : ℕ, Odd m ∧ 1 < m ∧ Quasiperfect (m ^ 2)) := by
  constructor
  · rintro ⟨n, hn, h⟩
    obtain ⟨m, hm⟩ := quasiperfect_isSquare hn h
    have hn2 : n = m ^ 2 := by rw [hm]; ring
    have hmodd : Odd m := by
      have hnodd : Odd n := quasiperfect_odd hn h
      rcases Nat.even_or_odd m with he | ho
      · exfalso
        rw [Nat.even_iff] at he
        rw [hn2, Nat.odd_iff, Nat.pow_mod, he] at hnodd
        simp at hnodd
      · exact ho
    have hm1 : 1 < m := by
      rcases Nat.lt_or_ge m 2 with hlt | hge
      · exfalso
        interval_cases m
        · simp at hn2
          omega
        · rw [hn2, Quasiperfect] at h
          norm_num [ArithmeticFunction.isMultiplicative_sigma.map_one] at h
      · omega
    exact ⟨m, hmodd, hm1, hn2 ▸ h⟩
  · rintro ⟨m, _, hm1, h⟩
    exact ⟨m ^ 2, pow_pos (by omega) 2, h⟩

end Brockian.QuasiperfectNumbers

