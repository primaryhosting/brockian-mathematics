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

namespace Brockian
namespace CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` which is a Fermat pseudoprime to every base,
i.e. `a ^ n ≡ a [MOD n]` for all `a`. -/

theorem isCarmichael_of_korselt {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r)
    (hp1 : p - 1 ∣ p * q * r - 1) (hq1 : q - 1 ∣ p * q * r - 1)
    (hr1 : r - 1 ∣ p * q * r - 1) : IsCarmichael (p * q * r) := by
  set n := p * q * r with hn
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have hpqr : 1 < n := by
    have : 1 < p * q := by nlinarith
    calc 1 < p * q := this
      _ ≤ p * q * r := Nat.le_mul_of_pos_right _ (by omega)
  have hcop_pq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (by omega)
  have hcop_pr : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr (by omega)
  have hcop_qr : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr (by omega)
  refine ⟨hpqr, ?_, ?_⟩
  · intro hprime
    have hdvd : p ∣ n := ⟨q * r, by rw [hn]; ring⟩
    rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
    · omega
    · have : p * (q * r) = p * 1 := by rw [← mul_assoc, ← hn, h, mul_one]
      have := Nat.eq_of_mul_eq_mul_left (by omega) this
      nlinarith
  · intro a
    have hmp := pow_modEq_self_of_sub_one_dvd hp (by omega) hp1 a
    have hmq := pow_modEq_self_of_sub_one_dvd hq (by omega) hq1 a
    have hmr := pow_modEq_self_of_sub_one_dvd hr (by omega) hr1 a
    have hpq' : a ^ n ≡ a [MOD p * q] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop_pq).mp ⟨hmp, hmq⟩
    have hcop : Nat.Coprime (p * q) r := Nat.Coprime.mul hcop_pr hcop_qr
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hpq', hmr⟩

/-- Chernick numbers: for `k ≥ 1`, if `6k+1`, `12k+1`, `18k+1` are all prime then their
product is a Carmichael number with exactly three (distinct) prime factors. -/
