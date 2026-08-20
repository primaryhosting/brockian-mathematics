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

theorem eq_six_of_unitaryPerfect_two_pow_mul_prime_pow {a p k : ℕ} (ha : 1 ≤ a) (hp : p.Prime)
    (hpodd : Odd p) (hk : 1 ≤ k) (h : IsUnitaryPerfect (2 ^ a * p ^ k)) : 2 ^ a * p ^ k = 6 := by
  have hPodd : Odd (p ^ k) := hpodd.pow
  have hPpos : 0 < p ^ k := pow_pos hp.pos k
  have hrel := (unitaryPerfect_two_pow_mul_iff ha hPodd hPpos).1 h
  rw [sigmaStar_prime_pow hp hk] at hrel
  have hA2 : 2 ≤ 2 ^ a := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hne : p ≠ 2 := by rintro rfl; simp [Nat.odd_iff] at hpodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hP3 : 3 ≤ p ^ k := by
    calc (3 : ℕ) ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
  have hkey : 2 ^ a + p ^ k + 1 = 2 ^ a * p ^ k := by
    have e1 : (2 ^ a + 1) * (p ^ k + 1) = 2 ^ a * p ^ k + (2 ^ a + p ^ k + 1) := by ring
    have e2 : 2 ^ (a + 1) * p ^ k = 2 ^ a * p ^ k + 2 ^ a * p ^ k := by rw [pow_succ]; ring
    rw [e1, e2] at hrel
    exact Nat.add_left_cancel hrel
  have hfin : 2 ^ a = 2 ∧ p ^ k = 3 := by
    constructor <;> nlinarith [hkey, hA2, hP3]
  rw [hfin.1, hfin.2]

