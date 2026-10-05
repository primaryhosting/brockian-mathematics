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

-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a module
-- docstring to precede the `import` block; the text is otherwise verbatim.)

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CarmichaelKorselt

/-- `n` is a Carmichael number: it is composite, yet `a ^ n ≡ a [ZMOD n]` for every integer `a`. -/

theorem isCarmichael_of_korselt_three {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hdp : (p - 1) ∣ (p * q * r - 1)) (hdq : (q - 1) ∣ (p * q * r - 1))
    (hdr : (r - 1) ∣ (p * q * r - 1)) : IsCarmichael (p * q * r) := by
  set n := p * q * r with hn
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have hn1 : 1 < n := by
    have h8 : 2 * 2 * 2 ≤ n := Nat.mul_le_mul (Nat.mul_le_mul hp2 hq2) hr2
    omega
  refine ⟨hn1, ?_, ?_⟩
  · intro hprime
    have hdvd : p ∣ n := ⟨q * r, by rw [hn]; ring⟩
    rcases Nat.Prime.eq_one_or_self_of_dvd hprime p hdvd with h | h
    · omega
    · have hqr1 : q * r = 1 := by
        have hp0 : 0 < p := by omega
        have hcalc : p * (q * r) = p * 1 :=
          calc p * (q * r) = p * q * r := by ring
            _ = n := hn.symm
            _ = p := h.symm
            _ = p * 1 := (mul_one p).symm
        exact Nat.eq_of_mul_eq_mul_left hp0 hcalc
      have hq1 : q ≤ 1 := Nat.le_of_dvd Nat.one_pos ⟨r, hqr1.symm⟩
      omega
  · intro a
    have hdp' := prime_dvd_pow_sub_self hp (by omega) hdp a
    have hdq' := prime_dvd_pow_sub_self hq (by omega) hdq a
    have hdr' := prime_dvd_pow_sub_self hr (by omega) hdr a
    have cpq : IsCoprime (p : ℤ) (q : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
    have cpr : IsCoprime (p : ℤ) (r : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hr).mpr hpr)
    have cqr : IsCoprime (q : ℤ) (r : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hr).mpr hqr)
    have h1 : ((p : ℤ) * q) ∣ a ^ n - a := cpq.mul_dvd hdp' hdq'
    have h2 : ((p : ℤ) * q * r) ∣ a ^ n - a := (cpr.mul_left cqr).mul_dvd h1 hdr'
    have hcast : ((n : ℕ) : ℤ) = (p : ℤ) * q * r := by rw [hn]; push_cast; ring
    rw [hcast]
    exact h2

/-- Chernick numbers `(6k+1)(12k+1)(18k+1)` with all three factors prime are Carmichael
numbers with exactly three prime factors. -/
