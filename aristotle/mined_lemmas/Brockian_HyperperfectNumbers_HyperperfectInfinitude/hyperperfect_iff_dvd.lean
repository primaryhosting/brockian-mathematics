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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

/-- `sigmaOne n` is the sum of the divisors of `n`. -/

lemma hyperperfect_iff_dvd {n : ℕ} (hn : n + 1 < sigmaOne n) :
    Hyperperfect n ↔ (sigmaOne n - (n + 1)) ∣ (n - 1) := by
  have hn2 : 2 ≤ n := by
    rcases n with _ | _ | n
    · simp [sigmaOne_zero] at hn
    · simp [sigmaOne_one] at hn
    · omega
  constructor
  · rintro ⟨k, hk, hEq⟩
    refine ⟨k, ?_⟩
    have h1 : ((n : ℤ) - 1) = ((sigmaOne n : ℤ) - ((n : ℤ) + 1)) * (k : ℤ) := by linarith
    have h2 : ((n - 1 : ℕ) : ℤ) = ((sigmaOne n - (n + 1) : ℕ) : ℤ) * (k : ℤ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : n + 1 ≤ sigmaOne n)]
      push_cast
      linarith
    exact_mod_cast h2
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | h
      · omega
      · exact h
    · have h2 : ((n - 1 : ℕ) : ℤ) = ((sigmaOne n - (n + 1) : ℕ) : ℤ) * (k : ℤ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hk
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : n + 1 ≤ sigmaOne n)] at h2
      push_cast at h2 ⊢
      linarith

/-! ## Concrete hyperperfect numbers (unconditional) -/

