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
def IsPrimeSpectrum (n : ℕ) (s : Multiset ℕ) : Prop :=
  (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n

/-- `n` admits a spectral model when it has a prime spectrum. -/
def HasSpectralModel (n : ℕ) : Prop :=
  ∃ s : Multiset ℕ, IsPrimeSpectrum n s

/-- **The Goldbach schema.**  From the *spectral model hypothesis* `hspec` (every integer
`≥ 2` admits a prime spectrum) one deduces the Goldbach-style conclusion: every integer
`n ≥ 2` is a sum of primes, and this sum consists of at least two primes whenever `n`
itself is not prime. -/
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
theorem spectral_model_exists : ∀ n : ℕ, 2 ≤ n → HasSpectralModel n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn1 : n ≠ 1 := by omega
    have hp : Nat.Prime n.minFac := Nat.minFac_prime hn1
    have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
    have hple : n.minFac ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hp2 : 2 ≤ n.minFac := hp.two_le
    rcases Nat.lt_or_ge (n - n.minFac) 2 with hlt | hge
    · -- remainder is `0` (it cannot be `1`)
      have hzero : n - n.minFac = 0 := by
        rcases Nat.lt_two_iff_zero_or_one.1 hlt with h | h
        · exact h
        · exfalso
          have hone : n.minFac ∣ 1 := by
            have h1 : n.minFac ∣ n - n.minFac := Nat.dvd_sub hdvd dvd_rfl
            rw [h] at h1
            exact h1
          have := Nat.le_of_dvd one_pos hone
          omega
      refine ⟨{n.minFac}, ?_, ?_⟩
      · intro q hq
        simp only [Multiset.mem_singleton] at hq
        exact hq ▸ hp
      · simp only [Multiset.sum_singleton]
        omega
    · obtain ⟨s, hs1, hs2⟩ := ih (n - n.minFac) (by omega) hge
      refine ⟨n.minFac ::ₘ s, ?_, ?_⟩
      · intro q hq
        rcases Multiset.mem_cons.1 hq with h | h
        · exact h ▸ hp
        · exact hs1 q h
      · rw [Multiset.sum_cons, hs2]
        omega

/-- **Goldbach from the spectral model, unconditionally.**  Every integer `n ≥ 2` is the
sum of a multiset of primes, and that multiset contains at least two primes whenever `n`
is not itself prime.  The spectral model hypothesis has been discharged by
`spectral_model_exists`. -/
theorem goldbach_from_spectral_model (n : ℕ) (hn : 2 ≤ n) :
    ∃ s : Multiset ℕ, IsPrimeSpectrum n s ∧ (¬ Nat.Prime n → 2 ≤ Multiset.card s) :=
  goldbach_schema spectral_model_exists n hn

end Brockian.GoldbachSchema

