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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian.SuperperfectNumbers

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/

lemma exists_prime_one_mod_four_dvd_of_sigma1_mod_four {m : ℕ} (hm : m ≠ 0)
    (h : sigma1 m % 4 = 2) : ∃ q, q.Prime ∧ q % 4 = 1 ∧ q ∣ m := by
  by_contra hcon
  push_neg at hcon
  by_cases hex : ∃ p ∈ m.primeFactors, 4 ∣ sigma1 (p ^ m.factorization p)
  · obtain ⟨p, hp, hdvd⟩ := hex
    have h4 : 4 ∣ sigma1 m := by
      rw [sigma1_factorization hm]
      exact hdvd.trans (Finset.dvd_prod_of_mem _ hp)
    omega
  · push_neg at hex
    have hodd : ∀ p ∈ m.primeFactors, Odd (sigma1 (p ^ m.factorization p)) := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      rcases eq_or_ne p 2 with rfl | hp2
      · exact sigma1_two_pow_odd _
      · have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two hp2)
        have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
        rcases h4 with h1 | h3
        · exact absurd (Nat.dvd_of_mem_primeFactors hp) (hcon p hpp h1)
        · have he : Even (m.factorization p) := by
            by_contra hne
            exact hex p hp (four_dvd_sigma1_primePow hpp h3 (Nat.not_even_iff_odd.mp hne))
          exact sigma1_odd_of_even_exp hpp hpodd he
    have hprod : Odd (sigma1 m) := by
      rw [sigma1_factorization hm]
      exact Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one hodd
    rw [Nat.odd_iff] at hprod
    omega

/-! ### Necessary conditions on an odd superperfect number -/

