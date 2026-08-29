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

lemma count_lt_count_iff {p : ℕ → Prop} [DecidablePred p] {a b : ℕ} (hab : a ≤ b) :
    Nat.count p a < Nat.count p b ↔ ∃ k, a ≤ k ∧ k < b ∧ p k := by
  induction b, hab using Nat.le_induction with
  | base => simp; omega
  | succ b hb ih =>
    rw [Nat.count_succ]
    constructor
    · intro h
      by_cases hpb : p b
      · exact ⟨b, hb, by omega, hpb⟩
      · rw [if_neg hpb] at h
        obtain ⟨k, hk1, hk2, hk3⟩ := ih.mp (by omega)
        exact ⟨k, hk1, by omega, hk3⟩
    · rintro ⟨k, hk1, hk2, hk3⟩
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hk2) with rfl | hlt
      · rw [if_pos hk3]
        have := Nat.count_monotone p hb
        omega
      · have := ih.mpr ⟨k, hk1, hlt, hk3⟩
        split <;> omega

