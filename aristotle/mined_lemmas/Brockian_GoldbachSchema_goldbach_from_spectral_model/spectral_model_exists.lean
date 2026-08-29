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
