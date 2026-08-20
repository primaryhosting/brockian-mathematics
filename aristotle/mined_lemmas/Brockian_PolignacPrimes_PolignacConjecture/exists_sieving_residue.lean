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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a module docstring because Lean 4 requires `import`
commands to precede every other command, including module docstrings.)

## Contents

* `PolignacProperty n` : there are infinitely many pairs of consecutive primes `(p, p+n)`.
* `DicksonTwoForms` : Dickson's conjecture for two linear forms with equal leading
  coefficients.
* `PolignacConjecture` : Dickson's conjecture implies Polignac's conjecture for every
  positive even gap. This is a Lean-checked conditional reduction of Polignac's
  conjecture (which is open) to a standard prime-tuple hypothesis.
* `not_polignacProperty_of_odd` : unconditionally, Polignac's property fails for odd gaps.
* `polignacProperty_two_iff_twinPrimes` : for gap `2` Polignac's property is exactly the
  twin prime conjecture.
-/

namespace Brockian.PolignacPrimes

/-- `p` and `q` are consecutive primes: both are prime, `p < q`, and no prime lies
strictly between them. -/

lemma exists_sieving_residue (n : ℕ) (hn : 2 ≤ n) :
    ∀ k : ℕ, k + 1 ≤ n →
      ∃ M a : ℕ, 0 < M ∧ Odd M ∧
        (∀ r : ℕ, Nat.Prime r → r ∣ M → ¬ r ∣ a ∧ ¬ r ∣ (a + n)) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ k → ∃ q : ℕ, Nat.Prime q ∧ n < q ∧ q ∣ M ∧ q ∣ (a + j)) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨1, 1, one_pos, odd_one,
      fun r hr hd => absurd (Nat.eq_one_of_dvd_one hd) hr.ne_one,
      fun j hj1 hj2 => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨M, a, hM0, hModd, hcop, hdiv⟩ := ih (by omega)
    obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (M + n + k + 2)
    have hqM : ¬ q ∣ M := fun h => absurd (Nat.le_of_dvd hM0 h) (by omega)
    obtain ⟨t, ht⟩ := exists_mul_add_dvd (a + (k + 1)) hq hqM
    have htq : q ∣ a + M * t + (k + 1) := by
      have h : a + M * t + (k + 1) = M * t + (a + (k + 1)) := by ring
      rwa [h]
    refine ⟨M * q, a + M * t, Nat.mul_pos hM0 hq.pos, ?_, ?_, ?_⟩
    · exact hModd.mul (hq.odd_of_ne_two (by omega))
    · intro r hr hrdvd
      rcases (Nat.Prime.dvd_mul hr).mp hrdvd with hrM | hrq
      · obtain ⟨h1, h2⟩ := hcop r hr hrM
        have hMt : r ∣ M * t := hrM.mul_right t
        refine ⟨fun h => h1 (by simpa using Nat.dvd_sub h hMt), fun h => h2 ?_⟩
        have hsub : r ∣ (a + M * t + n) - M * t := Nat.dvd_sub h hMt
        have heq : (a + M * t + n) - M * t = a + n := by omega
        rwa [heq] at hsub
      · have hrq' : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
        subst hrq'
        constructor
        · intro h
          have hsub : r ∣ (a + M * t + (k + 1)) - (a + M * t) := Nat.dvd_sub htq h
          have heq : (a + M * t + (k + 1)) - (a + M * t) = k + 1 := by omega
          rw [heq] at hsub
          exact absurd (Nat.le_of_dvd (by omega) hsub) (by omega)
        · intro h
          have hsub : r ∣ (a + M * t + n) - (a + M * t + (k + 1)) := Nat.dvd_sub h htq
          have heq : (a + M * t + n) - (a + M * t + (k + 1)) = n - (k + 1) := by omega
          rw [heq] at hsub
          exact absurd (Nat.le_of_dvd (by omega) hsub) (by omega)
    · intro j hj1 hj2
      rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
      · obtain ⟨p, hp, hpn, hpM, hpa⟩ := hdiv j hj1 (by omega)
        refine ⟨p, hp, hpn, hpM.mul_right q, ?_⟩
        have heq : a + M * t + j = (a + j) + M * t := by ring
        rw [heq]
        exact Nat.dvd_add hpa (hpM.mul_right t)
      · have hjeq : j = k + 1 := by omega
        subst hjeq
        exact ⟨q, hq, by omega, Dvd.intro_left M rfl, htq⟩

/-- Two distinct small shifts cannot both be roots of the same linear form mod `r`. -/
