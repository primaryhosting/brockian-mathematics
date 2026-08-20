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
/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists

(The header block above is repeated here as a module docstring: Lean requires `import`
commands to precede any doc comment, so the file-opening header is an ordinary comment.)

Unitary divisors, the unitary divisor sum `σ*`, unitary perfect numbers, verification of the
five known unitary perfect numbers, the fact that no odd number `> 1` is unitary perfect, and
a reduction of the open "sixth unitary perfect number" problem.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d ∣ n` with `gcd (d, n / d) = 1`. -/

theorem not_unitaryPerfect_of_odd {n : ℕ} (hodd : Odd n) (h1 : 1 < n) :
    ¬ IsUnitaryPerfect n := by
  rintro ⟨-, hperf⟩
  set p := n.minFac with hpdef
  have hn0 : n ≠ 0 := by omega
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ n := Nat.minFac_dvd n
  have hk : 0 < n.factorization p := hp.factorization_pos_of_dvd hn0 hpdvd
  set k := n.factorization p with hkdef
  set m := n / p ^ k with hmdef
  have hsplit : p ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : Nat.Coprime (p ^ k) m := (Nat.coprime_ordCompl hp hn0).pow_left _
  have hpos : 0 < m := Nat.ordCompl_pos p hn0
  have hs : sigmaStar n = (p ^ k + 1) * sigmaStar m := by
    conv_lhs => rw [← hsplit]
    exact sigmaStar_prime_pow_mul hp hk hpos hcop
  have hpodd : Odd p := hodd.of_dvd_nat hpdvd
  have hppow : Odd (p ^ k) := hpodd.pow
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hpos.ne') with h | hm1
  · -- `m = 1`, so `n = p ^ k` and `p ^ k + 1 = 2 p ^ k` forces `p ^ k = 1`
    have hm : m = 1 := h.symm
    have hnp : n = p ^ k := by rw [← hsplit, hm, mul_one]
    rw [hs, hm, sigmaStar_one, mul_one, hnp] at hperf
    have : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
    omega
  · -- `m > 1` is odd, so `σ*(m)` is even and `4 ∣ σ*(n) = 2 n`, contradicting `n` odd
    have hmodd : Odd m := hodd.of_dvd_nat ⟨p ^ k, by rw [← hsplit]; ring⟩
    obtain ⟨c, hc⟩ := even_sigmaStar_of_odd hmodd hm1
    obtain ⟨t, ht⟩ := hppow
    obtain ⟨u, hu⟩ := hodd
    have hexp : (p ^ k + 1) * sigmaStar m = 4 * ((t + 1) * c) := by rw [hc, ht]; ring
    rw [hs, hexp, hu] at hperf
    omega

