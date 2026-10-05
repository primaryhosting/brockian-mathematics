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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` such that `a ^ (n - 1) ≡ 1 [MOD n]` for every
`a` coprime to `n` (i.e. a Fermat pseudoprime to every admissible base). -/

theorem isCarmichael_of_korselt {n : ℕ} (h1 : 1 < n) (hnp : ¬ n.Prime) (hsq : Squarefree n)
    (hk : ∀ p ∈ n.primeFactors, (p - 1) ∣ (n - 1)) : IsCarmichael n := by
  refine ⟨h1, hnp, fun a ha => ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at ha
    omega
  have hpow : 1 ≤ a ^ (n - 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero ha0)
  have hdvd : n ∣ a ^ (n - 1) - 1 := by
    refine dvd_of_squarefree_of_forall_prime_dvd hsq ?_
    · intro p hp
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hap : Nat.Coprime a p := Nat.Coprime.coprime_dvd_right hpn ha
      obtain ⟨t, ht⟩ := hk p hp
      have hfermat : a ^ (p - 1) ≡ 1 [MOD p] := by
        have := Nat.ModEq.pow_totient hap
        rwa [Nat.totient_prime hprime] at this
      have : a ^ (n - 1) ≡ 1 [MOD p] := by
        calc a ^ (n - 1) = (a ^ (p - 1)) ^ t := by rw [← pow_mul, ← ht]
          _ ≡ 1 ^ t [MOD p] := hfermat.pow t
          _ = 1 := one_pow t
      exact (Nat.modEq_iff_dvd' hpow).mp this.symm
  exact ((Nat.modEq_iff_dvd' hpow).mpr hdvd).symm

/-- The three prime factors in Chernick's construction are pairwise distinct (for `k ≥ 1`). -/
