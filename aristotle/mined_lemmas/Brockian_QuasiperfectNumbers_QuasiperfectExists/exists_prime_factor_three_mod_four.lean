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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of its divisors equals `2 * n + 1`,
i.e. the sum of its proper divisors is `n + 1`. -/

lemma exists_prime_factor_three_mod_four :
    ∀ n : ℕ, n % 4 = 3 → ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn1 : n ≠ 1 := by omega
    set p := n.minFac with hp
    have hpp : p.Prime := Nat.minFac_prime hn1
    obtain ⟨q, hq⟩ : p ∣ n := Nat.minFac_dvd n
    have hpodd : p % 2 = 1 := by
      rcases hpp.eq_two_or_odd with h2 | h2
      · exfalso; rw [h2] at hq; omega
      · exact h2
    rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h1 | h3
    · have hq4 : q % 4 = 3 := by
        have hnq : n % 4 = q % 4 := by
          rw [hq, Nat.mul_mod, h1, one_mul, Nat.mod_mod]
        omega
      have hqlt : q < n := by
        have hp3 : 3 ≤ p := by have := hpp.two_le; omega
        have hq3 : 3 ≤ q := by omega
        calc q < 3 * q := by omega
          _ ≤ p * q := Nat.mul_le_mul_right q hp3
          _ = n := hq.symm
      obtain ⟨r, hr, hrd, hr4⟩ := ih q hqlt hq4
      exact ⟨r, hr, hrd.trans ⟨p, by rw [hq]; ring⟩, hr4⟩
    · exact ⟨p, hpp, Nat.minFac_dvd n, h3⟩

/-- If `p` is a prime congruent to `3` mod `4`, then `p` does not divide `t ^ 2 + 1`. -/
