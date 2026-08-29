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

/-!
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.GoldbachSchema

/-- A *prime spectrum* of `n` is a multiset `s` of primes (the "spectral lines", with
multiplicity) whose total mass `s.sum` is exactly `n`. -/

theorem goldbach_schema
    (hspec : ∀ m : ℕ, 2 ≤ m → HasSpectralModel m)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ s : Multiset ℕ, IsPrimeSpectrum n s ∧ (¬ Nat.Prime n → 2 ≤ Multiset.card s) := by
  obtain ⟨s, hprime, hsum⟩ := hspec n hn
  refine ⟨s, ⟨hprime, hsum⟩, ?_⟩
  intro hnp
  by_contra hcard
  push_neg at hcard
  interval_cases h : (Multiset.card s)
  · rw [Multiset.card_eq_zero] at h
    subst h
    simp only [Multiset.sum_zero] at hsum
    omega
  · obtain ⟨p, hp⟩ := Multiset.card_eq_one.1 h
    subst hp
    simp only [Multiset.sum_singleton] at hsum
    exact hnp (hsum ▸ hprime p (by simp))

/-- **Discharge of the spectral model hypothesis.**  Every integer `n ≥ 2` admits a prime
spectrum.  Proved by strong induction on `n`: peel off the least prime factor `p` of `n`;
the remainder `n - p` is either `0` or again `≥ 2` (it cannot be `1`, since `p ∣ n` and
`p ∣ n - 1` would force `p ∣ 1`), and it is strictly smaller than `n`. -/
