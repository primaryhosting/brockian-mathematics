/-
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
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

/-! ### A kernel-friendly primality test

Mathlib's `Nat.decidablePrime` instance tests every candidate divisor below `n`, which makes
`by decide` too slow for a few hundred numbers of size ~1300.  We therefore use trial division by
the divisors `d` with `d * d ≤ n`, together with the correctness lemma `isPrimeB_prime`. -/

/-- `trialDivB n k = true` iff no `d ≤ k` with `2 ≤ d` and `d * d ≤ n` divides `n`. -/

lemma trialDivB_spec (n : ℕ) : ∀ (k d : ℕ), trialDivB n k = true → 2 ≤ d → d ≤ k →
    d * d ≤ n → ¬ (d ∣ n) := by
  intro k
  induction k with
  | zero => intro d _ _ hd; omega
  | succ k ih =>
      intro d h h2 hd hdd
      rw [trialDivB, Bool.and_eq_true] at h
      obtain ⟨h1, h3⟩ := h
      rcases Nat.lt_or_ge d (k + 1) with hlt | hge
      · exact ih d h3 h2 (by omega) hdd
      · have hk : d = k + 1 := by omega
        subst hk
        intro hdvd
        simp [h2, hdd] at h1
        exact h1 (Nat.dvd_iff_mod_eq_zero.mp hdvd)

/-- Boolean primality test, correct for all `n ≤ 36 ^ 2 + 36 = 1368`. -/
