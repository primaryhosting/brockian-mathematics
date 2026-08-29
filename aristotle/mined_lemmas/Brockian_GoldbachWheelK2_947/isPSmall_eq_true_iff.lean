/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- rendered as a plain block comment; the identical module docstring follows the import.)

import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 400000
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

/-- A kernel-friendly primality test: trial division by all candidate divisors `< 47`.
It is a correct primality test for every `n < 47 ^ 2 = 2209`, see `Brockian.isPSmall_iff`. -/

theorem isPSmall_eq_true_iff (n : ℕ) :
    isPSmall n = true ↔ (2 ≤ n ∧ ∀ m, m < 47 → 2 ≤ m → m < n → n % m ≠ 0) := by
  simp only [isPSmall, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun m hm h2m hmn => ?_⟩
    rcases h2 m hm with (h | h) | h <;> omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun m hm => ?_⟩
    by_cases h2m : 2 ≤ m
    · by_cases hmn : m < n
      · exact Or.inr (h2 m hm h2m hmn)
      · exact Or.inl (Or.inr (by omega))
    · exact Or.inl (Or.inl (by omega))

/-- Correctness of `Brockian.isPSmall` below `2209 = 47 ^ 2`. -/
