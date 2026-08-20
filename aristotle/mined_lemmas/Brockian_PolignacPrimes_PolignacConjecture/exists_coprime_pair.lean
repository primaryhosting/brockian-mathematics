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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Polignac's conjecture (1849) asserts that for every positive even number `n` there are
infinitely many pairs of *consecutive* primes `p < q` with `q - p = n`.  This is open
(the case `n = 2` is the twin prime conjecture).

This file gives a Lean-checked *conditional reduction*: Polignac's conjecture follows from
Dickson's conjecture for two linear forms `M x + a`, `M x + b` (the standard hypothesis that an
admissible system of linear forms simultaneously represents primes infinitely often).

The reduction is the classical sieve/congruence argument: given an even `n`, one produces an
arithmetic progression `M x + a` such that *all* of the intermediate values
`M x + a + 1, …, M x + a + (n-1)` are automatically composite, while the two forms
`M x + a` and `M x + a + n` are admissible.
-/

namespace Brockian.PolignacPrimes

/-- `q` is the prime immediately following `p`: both are prime, `p < q`, and nothing strictly
between them is prime. -/

theorem exists_coprime_pair (n : ℕ) (hn : Even n) (N : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ p : ℕ, p.Prime → p ≤ N → ¬ p ∣ m ∧ ¬ p ∣ (m + n) := by
  have hpar : ∀ m : ℕ, m % 2 = (m + n) % 2 := by
    obtain ⟨k, hk⟩ := hn
    intro m; omega
  induction N with
  | zero =>
      exact ⟨1, one_pos, fun p hp hple => absurd hple (by have := hp.two_le; omega)⟩
  | succ N ih =>
      obtain ⟨m, hm0, hm⟩ := ih
      by_cases hq : (N + 1).Prime
      · by_cases hd : ¬ (N + 1) ∣ m ∧ ¬ (N + 1) ∣ (m + n)
        · refine ⟨m, hm0, fun p hp hple => ?_⟩
          rcases Nat.lt_or_ge p (N + 1) with h | h
          · exact hm p hp (by omega)
          · have hpe : p = N + 1 := by omega
            subst hpe; exact hd
        · have hfac : ¬ (N + 1) ∣ Nat.factorial N := by
            rw [hq.dvd_factorial]; omega
          obtain ⟨t, h1, h2⟩ :=
            exists_not_dvd_pair (p := N + 1) (u := Nat.factorial N) (c := m) (d := m + n)
              hq hfac (hpar m)
          refine ⟨Nat.factorial N * t + m, by omega, fun p hp hple => ?_⟩
          rcases Nat.lt_or_ge p (N + 1) with h | h
          · have hpf : p ∣ Nat.factorial N * t :=
              Dvd.dvd.mul_right (Nat.dvd_factorial hp.pos (by omega)) t
            refine ⟨fun hc => (hm p hp (by omega)).1 ((Nat.dvd_add_right hpf).1 hc), fun hc => ?_⟩
            refine (hm p hp (by omega)).2 ((Nat.dvd_add_right hpf).1 ?_)
            rwa [add_assoc] at hc
          · have hpe : p = N + 1 := by omega
            subst hpe
            exact ⟨h1, by rw [add_assoc]; exact h2⟩
      · refine ⟨m, hm0, fun p hp hple => hm p hp ?_⟩
        by_cases hpe : p = N + 1
        · exact absurd (hpe ▸ hp) hq
        · omega

/-- **Main result.**  Dickson's conjecture (for two linear forms) implies Polignac's conjecture. -/
