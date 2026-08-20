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

theorem even_sigmaStar_of_odd {m : ℕ} (hodd : Odd m) (h1 : 1 < m) : Even (sigmaStar m) := by
  set p := m.minFac with hpdef
  have hm0 : m ≠ 0 := by omega
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ m := Nat.minFac_dvd m
  have hk : 0 < m.factorization p := hp.factorization_pos_of_dvd hm0 hpdvd
  have hsplit : p ^ m.factorization p * (m / p ^ m.factorization p) = m :=
    Nat.ordProj_mul_ordCompl_eq_self m p
  have hcop : Nat.Coprime (p ^ m.factorization p) (m / p ^ m.factorization p) :=
    (Nat.coprime_ordCompl hp hm0).pow_left _
  have hpos : 0 < m / p ^ m.factorization p := Nat.ordCompl_pos p hm0
  have hs : sigmaStar m = (p ^ m.factorization p + 1) * sigmaStar (m / p ^ m.factorization p) := by
    conv_lhs => rw [← hsplit]
    exact sigmaStar_prime_pow_mul hp hk hpos hcop
  have hpodd : Odd p := hodd.of_dvd_nat hpdvd
  have : Odd (p ^ m.factorization p) := hpodd.pow
  rw [hs]
  exact (Odd.add_one this).mul_right _

