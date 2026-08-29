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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset Pointwise

/-! ## Basic definitions -/

/-- The sum of the (positive) divisors of `n`. -/

lemma covers_mul_coprime : ∀ m n : ℕ, Covers n → 0 < m → Nat.Coprime m n →
    m ≤ sigma1 n + 1 → Covers (n * m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hcovn hm hcop hle
    by_cases hm1 : m = 1
    · simpa [hm1] using hcovn
    · have hm2 : 2 ≤ m := by omega
      set p := m.minFac with hp'
      have hp : p.Prime := Nat.minFac_prime hm1
      have hpm : p ∣ m := Nat.minFac_dvd m
      set e := m.factorization p with he
      set m' := m / p ^ e with hm'
      have hsplit : p ^ e * m' = m := Nat.ordProj_mul_ordCompl_eq_self m p
      have hpm' : ¬ p ∣ m' := Nat.not_dvd_ordCompl hp (by omega)
      have hepos : 0 < e := hp.factorization_pos_of_dvd (by omega) hpm
      have hm'pos : 0 < m' := Nat.ordCompl_pos p (by omega)
      have hpe2 : 2 ≤ p ^ e := by
        calc 2 ≤ p := hp.two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos hepos
      have hm'lt : m' < m := by nlinarith
      have hpn : ¬ p ∣ n := by
        intro hdvd
        have : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm hdvd
        rw [hcop] at this
        exact hp.ne_one (Nat.dvd_one.mp this)
      have hpsig : p ≤ sigma1 n + 1 := le_trans (Nat.minFac_le (by omega)) hle
      have hcov2 : Covers (n * p ^ e) := hcovn.mul_prime_pow hp hpn hpsig e
      have hdvd : n ∣ n * p ^ e := Dvd.intro _ rfl
      have hsig : sigma1 n ≤ sigma1 (n * p ^ e) :=
        sigma1_le_of_dvd (Nat.mul_pos hcovn.1 (pow_pos hp.pos _)) hdvd
      have hcop' : Nat.Coprime m' (n * p ^ e) := by
        refine Nat.Coprime.mul_right ?_ ?_
        · exact Nat.Coprime.coprime_dvd_left ⟨p ^ e, by rw [← hsplit]; ring⟩ hcop
        · exact Nat.Coprime.pow_right _ (((hp.coprime_iff_not_dvd).mpr hpm').symm)
      have := ih m' hm'lt (n * p ^ e) hcov2 hm'pos hcop' (by omega)
      have heq : n * p ^ e * m' = n * m := by rw [mul_assoc, hsplit]
      rwa [heq] at this

/-! ## Sigma of prime powers times a base -/

