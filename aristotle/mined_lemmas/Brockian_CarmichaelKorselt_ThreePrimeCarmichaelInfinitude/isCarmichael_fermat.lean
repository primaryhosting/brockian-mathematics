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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace CarmichaelKorselt

/-- Korselt's criterion, used here as the definition of a Carmichael number:
`n` is composite (`1 < n` and not prime), squarefree, and `p - 1 ∣ n - 1` for every
prime `p` dividing `n`. -/

theorem isCarmichael_fermat {n : ℕ} (hn : IsCarmichael n) (a : ℕ) :
    a ^ n ≡ a [MOD n] := by
  obtain ⟨h1, -, hsq, hkor⟩ := hn
  have hpos : 0 < n := lt_trans Nat.zero_lt_one h1
  -- for each prime factor `p` of `n`, `p ∣ a ^ n - a`
  have key : ∀ p ∈ n.primeFactors, p ∣ a ^ n - a := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hle : a ≤ a ^ n := Nat.le_self_pow hpos.ne' a
    have hmod : a ≡ a ^ n [MOD p] := by
      by_cases hdvd : p ∣ a
      · have h1' : a ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hdvd
        have h2' : a ^ n ≡ 0 ^ n [MOD p] := h1'.pow n
        rw [zero_pow hpos.ne'] at h2'
        exact h1'.trans h2'.symm
      · have hcop : Nat.Coprime a p := ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hdvd).symm
        obtain ⟨m, hm⟩ := hkor p hp
        have hfermat : a ^ (p - 1) ≡ 1 [MOD p] := by
          have := Nat.ModEq.pow_totient hcop
          rwa [Nat.totient_prime hpp] at this
        have hpow : a ^ (n - 1) ≡ 1 [MOD p] := by
          have : a ^ (n - 1) = (a ^ (p - 1)) ^ m := by rw [← pow_mul, ← hm]
          rw [this]
          simpa using hfermat.pow m
        have : a ^ (n - 1) * a ≡ 1 * a [MOD p] := hpow.mul_right a
        have heq : a ^ (n - 1) * a = a ^ n := by
          rw [← pow_succ]
          congr 1
          omega
        rw [heq, one_mul] at this
        exact this.symm
    exact (Nat.modEq_iff_dvd' hle).mp hmod
  have hprod : ∏ p ∈ n.primeFactors, p ∣ a ^ n - a :=
    Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      (fun p hp => key p hp)
  rw [Nat.prod_primeFactors_of_squarefree hsq] at hprod
  have hle : a ≤ a ^ n := Nat.le_self_pow hpos.ne' a
  exact ((Nat.modEq_iff_dvd' hle).mpr hprod).symm

/-- If `n > 1` is a Fermat pseudoprime to every base, then `n` is squarefree. -/
