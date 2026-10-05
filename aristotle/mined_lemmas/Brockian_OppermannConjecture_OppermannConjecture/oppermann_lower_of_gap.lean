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
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Oppermann's conjecture is open, so the main result here is a Lean-checked *conditional
reduction*: Oppermann's conjecture follows from a Legendre-type prime gap hypothesis
(`SqrtPrimeGap`), together with an unconditional verification of the small cases
`2 ≤ n ≤ 40`.
-/

namespace Brockian.OppermannConjecture

/-- **Oppermann's conjecture**: for every `n ≥ 2` there is a prime strictly between
`n(n-1)` and `n²`, and a prime strictly between `n²` and `n(n+1)`. -/

theorem oppermann_lower_of_gap (h : SqrtPrimeGap) (n : ℕ) (hn : 11 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n * (n - 1) < p ∧ p < n * n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
  have hsub : (k + 11) - 1 = k + 10 := by omega
  rw [hsub]
  set m := (k + 11) * (k + 10) with hm
  have hm100 : 100 ≤ m := by simp only [hm]; nlinarith
  obtain ⟨p, hp, hlt, hle⟩ := h m hm100
  refine ⟨p, hp, hlt, ?_⟩
  have hsqrt : Nat.sqrt m ≤ k + 10 := by
    have : Nat.sqrt m < k + 11 := by
      rw [Nat.sqrt_lt]
      simp only [hm]; nlinarith
    omega
  have hp' : p ≤ m + (k + 10) := le_trans hle (by omega)
  simp only [hm] at hp' ⊢
  nlinarith

/-- For `n ≥ 11` the upper Oppermann interval `(n², n(n+1))` follows from `SqrtPrimeGap`. -/
