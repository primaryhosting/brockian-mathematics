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
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RieselCovering

/-- A *Riesel number* is a positive odd natural number `k` such that `k * 2 ^ n - 1`
is composite (never prime) for every `n ≥ 1`. -/

theorem riesel_509203 : IsRieselNumber 509203 := by
  refine ⟨by norm_num, ⟨254601, by norm_num⟩, ?_⟩
  intro n hn hprime
  -- a lower bound on the number in question
  have hbig : 1018405 ≤ 509203 * 2 ^ n - 1 := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  -- find the covering prime
  have hlt : n % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have key : ∃ p : ℕ, p ∣ 509203 * 2 ^ n - 1 ∧ 1 < p ∧ p ≤ 241 := by
    interval_cases h : n % 24 <;>
      [ exact ⟨3, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨5, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨3, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨241, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨3, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨5, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨3, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨13, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨3, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨5, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨3, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨7, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨3, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨5, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨3, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨17, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨3, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨5, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨3, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨13, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨3, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨5, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨3, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩;
        exact ⟨7, covering_dvd (by norm_num) h (by norm_num), by norm_num, by norm_num⟩ ]
  obtain ⟨p, hdvd, hp1, hp2⟩ := key
  rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p hdvd) with h | h <;> omega

/-- **Riesel problem** (covering-set half): there exists a positive odd `k`
with `k * 2 ^ n - 1` composite for all `n ≥ 1`; explicitly `k = 509203`. -/
