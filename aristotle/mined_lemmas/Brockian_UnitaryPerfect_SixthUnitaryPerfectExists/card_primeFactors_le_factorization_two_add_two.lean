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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: divisors `d` with `gcd (d, n / d) = 1`. -/

theorem card_primeFactors_le_factorization_two_add_two {n : ℕ} (h : IsUnitaryPerfect n) :
    n.primeFactors.card ≤ n.factorization 2 + 2 := by
  obtain ⟨hpos, heq⟩ := h
  have hn0 : n ≠ 0 := hpos.ne'
  have h2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two,
      (even_iff_two_dvd.mp (even_of_isUnitaryPerfect ⟨hpos, heq⟩)), hn0⟩
  have hdvd : (2 : ℕ) ^ (n.primeFactors.card - 1) ∣ usigma n := by
    rw [usigma_eq_prod hn0, ← Finset.prod_erase_mul _ _ h2]
    refine Dvd.dvd.mul_right ?_ _
    have hcard : (n.primeFactors.erase 2).card = n.primeFactors.card - 1 :=
      Finset.card_erase_of_mem h2
    rw [← hcard, ← Finset.prod_const]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    exact even_iff_two_dvd.mp (Odd.add_one ((hpp.odd_of_ne_two (Finset.ne_of_mem_erase hp)).pow))
  rw [heq] at hdvd
  have hfac : (2 * n).factorization 2 = 1 + n.factorization 2 := by
    rw [Nat.factorization_mul (by norm_num) hn0]
    simp [Nat.Prime.factorization_self Nat.prime_two]
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by positivity)).mp hdvd
  rw [hfac] at hle
  have h1 : 1 ≤ n.primeFactors.card := Finset.card_pos.mpr ⟨2, h2⟩
  omega

