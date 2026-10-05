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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AndricaConjecture

open Real

/-- `prime n` is the `n`-th prime number (`prime 0 = 2`, `prime 1 = 3`, ...). -/

theorem gap_bound_of_oppermann (hOpp : OppermannConjecture) {n : ℕ} (hn : 2 ≤ n) :
    (prime (n + 1) : ℝ) < (prime n : ℝ) + 2 * Real.sqrt (prime n) + 1 := by
  set a := prime n with ha
  set b := prime (n + 1) with hb
  set k := Nat.sqrt a with hk
  have ha5 : 5 ≤ a := five_le_prime hn
  have hk2 : 2 ≤ k := Nat.le_sqrt.2 (by omega)
  have hkk : k * k ≤ a := Nat.sqrt_le a
  have hka : a < (k + 1) * (k + 1) := Nat.lt_succ_sqrt a
  have hexp : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
  have hkR : (k : ℝ) ≤ Real.sqrt a := by
    rw [show ((k : ℝ)) = Real.sqrt ((k : ℝ) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have : ((k * k : ℕ) : ℝ) ≤ (a : ℝ) := Nat.cast_le.2 hkk
    push_cast at this ⊢
    nlinarith
  obtain ⟨⟨q1, hq1p, hq1l, hq1r⟩, ⟨q2, hq2p, hq2l, hq2r⟩⟩ := hOpp (k + 1) (by omega)
  rcases Nat.lt_or_ge a (k * k + k + 1) with hcase | hcase
  · -- Case A : `a ≤ k² + k`; use the prime in `((k+1)² - (k+1), (k+1)²)`
    have hle : b ≤ q1 := prime_succ_le hq1p (by omega)
    have hbnat : b ≤ a + 2 * k := by omega
    have hbR : (b : ℝ) ≤ (a : ℝ) + 2 * (k : ℝ) := by exact_mod_cast Nat.cast_le.2 hbnat
    linarith
  · -- Case B : `a ≥ k² + k + 1`; use the prime in `((k+1)², (k+1)² + (k+1))`
    have hle : b ≤ q2 := prime_succ_le hq2p (by omega)
    have hbnat : b ≤ k * k + 3 * k + 1 := by omega
    have haR : (k : ℝ) * (k : ℝ) + (k : ℝ) + 1 ≤ (a : ℝ) := by
      have : ((k * k + k + 1 : ℕ) : ℝ) ≤ (a : ℝ) := Nat.cast_le.2 (by omega)
      push_cast at this
      linarith
    have hsqrt : (k : ℝ) + 1 / 2 < Real.sqrt a :=
      (Real.lt_sqrt (by positivity)).2 (by nlinarith)
    have hbR : (b : ℝ) ≤ (k : ℝ) * (k : ℝ) + 3 * (k : ℝ) + 1 := by
      have : ((b : ℕ) : ℝ) ≤ ((k * k + 3 * k + 1 : ℕ) : ℝ) := Nat.cast_le.2 hbnat
      push_cast at this
      linarith
    linarith

/-! ## Main result -/

/-- **Andrica's conjecture**, conditional on Oppermann's conjecture: for all `n`,
`√pₙ₊₁ - √pₙ < 1`, where `pₙ` denotes the `n`-th prime.

Andrica's conjecture is a well-known open problem; what is established here is the
unconditional implication `Oppermann ⟹ Andrica`, together with the unconditional
verification of the first two cases. -/
