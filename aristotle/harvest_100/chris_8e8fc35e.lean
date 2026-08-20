/-!
# Quadruplet 11 13 17 19
Category: Frontier — Prime Numbers
Target: Constellation.quadruplet_11_13_17_19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Constellation

/-- Primality of a natural number, spelled out elementarily: `n` is at least `2`
and every divisor of `n` is either `1` or `n`.

This is stated without any `import` because Lean requires every `import` command to
precede all other syntax in a file, including the module docstring above; the file
`RequestProject/Quadruplet11131719Mathlib.lean` proves that `IsPrimeNat` is equivalent
to Mathlib's `Nat.Prime`, and restates the theorem below in those terms. -/
def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

theorem isPrimeNat_of_bounded {n : Nat} (h2 : 2 ≤ n)
    (h : ∀ m, m < n + 1 → m ∣ n → m = 1 ∨ m = n) : IsPrimeNat n := by
  refine ⟨h2, fun m hm => h m ?_ hm⟩
  exact Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hm)

/-- `(11, 13, 17, 19)` is a prime quadruplet of pattern `(0, 2, 6, 8)`: each of
`11`, `13`, `17`, `19` is prime, and `13 = 11 + 2`, `17 = 11 + 6`, `19 = 11 + 8`. -/
theorem quadruplet_11_13_17_19 :
    IsPrimeNat 11 ∧ IsPrimeNat 13 ∧ IsPrimeNat 17 ∧ IsPrimeNat 19 ∧
      13 = 11 + 2 ∧ 17 = 11 + 6 ∧ 19 = 11 + 8 :=
  ⟨isPrimeNat_of_bounded (by omega) (by decide),
   isPrimeNat_of_bounded (by omega) (by decide),
   isPrimeNat_of_bounded (by omega) (by decide),
   isPrimeNat_of_bounded (by omega) (by decide),
   rfl, rfl, rfl⟩

end Constellation

import Mathlib
import RequestProject.Quadruplet11131719

/-!
# Quadruplet 11 13 17 19 — Mathlib bridge

`Constellation.IsPrimeNat` agrees with Mathlib's `Nat.Prime`, so the theorem
`Constellation.quadruplet_11_13_17_19` is the statement that `(11, 13, 17, 19)`
is a prime quadruplet of pattern `(0, 2, 6, 8)`.
-/

namespace Constellation

/-- The elementary primality predicate used in `Quadruplet11131719.lean` coincides
with Mathlib's `Nat.Prime` (`Nat.prime_def_lt`-style characterisation). -/
theorem isPrimeNat_iff_nat_prime (n : Nat) : IsPrimeNat n ↔ Nat.Prime n :=
  ⟨fun ⟨h2, h⟩ => (Nat.prime_def.2 ⟨h2, h⟩), fun hp => ⟨hp.two_le, fun _ hm => (Nat.Prime.eq_one_or_self_of_dvd hp _ hm)⟩⟩

/-- Mathlib-flavoured restatement: `(11, 13, 17, 19)` is a prime quadruplet with
pattern `(0, 2, 6, 8)`. -/
theorem quadruplet_11_13_17_19_nat_prime :
    Nat.Prime 11 ∧ Nat.Prime 13 ∧ Nat.Prime 17 ∧ Nat.Prime 19 ∧
      13 = 11 + 2 ∧ 17 = 11 + 6 ∧ 19 = 11 + 8 := by
  obtain ⟨h11, h13, h17, h19, e1, e2, e3⟩ := quadruplet_11_13_17_19
  exact ⟨(isPrimeNat_iff_nat_prime 11).1 h11, (isPrimeNat_iff_nat_prime 13).1 h13,
    (isPrimeNat_iff_nat_prime 17).1 h17, (isPrimeNat_iff_nat_prime 19).1 h19, e1, e2, e3⟩

end Constellation

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

