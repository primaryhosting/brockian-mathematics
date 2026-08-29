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

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Brockian.OppermannConjecture

/-- Oppermann's property for `n`: there is a prime strictly between `n(n-1)` and `n²`,
and a prime strictly between `n²` and `n(n+1)`. -/

theorem oppermannProperty_iff_primeCounting (n : ℕ) (h2 : 2 ≤ n) :
    OppermannProperty n ↔
      Nat.primeCounting (n * n - n) < Nat.primeCounting (n * n) ∧
        Nat.primeCounting (n * n) < Nat.primeCounting (n * n + n) := by
  have hnn : n + n ≤ n * n := by nlinarith
  have e₁ : Nat.primeCounting (n * n - n) < Nat.primeCounting (n * n) ↔
      ∃ k, n * n - n + 1 ≤ k ∧ k < n * n + 1 ∧ Nat.Prime k := by
    simpa [Nat.primeCounting, Nat.primeCounting'] using
      count_lt_count_iff (p := Nat.Prime) (a := n * n - n + 1) (b := n * n + 1) (by omega)
  have e₂ : Nat.primeCounting (n * n) < Nat.primeCounting (n * n + n) ↔
      ∃ k, n * n + 1 ≤ k ∧ k < n * n + n + 1 ∧ Nat.Prime k := by
    simpa [Nat.primeCounting, Nat.primeCounting'] using
      count_lt_count_iff (p := Nat.Prime) (a := n * n + 1) (b := n * n + n + 1) (by omega)
  rw [OppermannProperty, e₁, e₂]
  constructor
  · rintro ⟨⟨p, hp, hp1, hp2⟩, ⟨q, hq, hq1, hq2⟩⟩
    exact ⟨⟨p, by omega, by omega, hp⟩, ⟨q, by omega, by omega, hq⟩⟩
  · rintro ⟨⟨p, hp1, hp2, hp⟩, ⟨q, hq1, hq2, hq⟩⟩
    refine ⟨⟨p, hp, by omega, ?_⟩, ⟨q, hq, by omega, ?_⟩⟩
    · rcases Nat.lt_or_ge p (n * n) with h | h
      · exact h
      · have : p = n * n := by omega
        exact absurd (this ▸ hp) (not_prime_mul_self h2)
    · rcases Nat.lt_or_ge q (n * n + n) with h | h
      · exact h
      · have : q = n * n + n := by omega
        exact absurd (this ▸ hq) (not_prime_mul_succ h2)

end Brockian.OppermannConjecture

