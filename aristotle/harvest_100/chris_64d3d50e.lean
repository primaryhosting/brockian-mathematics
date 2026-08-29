/-
# Fermat Little
Category: Pure Mathematics
Target: Math.fermat_little
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fermat Little
Category: Pure Mathematics
Target: Math.fermat_little
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- **Fermat's little theorem** (integer form): if `p` is prime and `p` does not divide `a`,
then `a ^ (p - 1) ≡ 1 (mod p)`. -/
theorem fermat_little {p : ℕ} (hp : Nat.Prime p) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    a ^ (p - 1) ≡ 1 [ZMOD (p : ℤ)] := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime a (p : ℤ) :=
    IsCoprime.symm ((Prime.coprime_iff_not_dvd (R := ℤ) hpp).mpr ha)
  exact Int.ModEq.pow_card_sub_one_eq_one hp hcop

/-- **Fermat's little theorem** (natural number form): if `p` is prime and `p` does not divide `a`,
then `a ^ (p - 1) ≡ 1 [MOD p]`. -/
theorem fermat_little_nat {p a : ℕ} (hp : Nat.Prime p) (ha : ¬ p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have ha' : ¬ (p : ℤ) ∣ (a : ℤ) := by
    simpa [Int.natCast_dvd_natCast] using ha
  have h := fermat_little hp ha'
  have : ((a ^ (p - 1) : ℕ) : ℤ) ≡ ((1 : ℕ) : ℤ) [ZMOD (p : ℤ)] := by
    push_cast
    exact h
  exact Int.natCast_modEq_iff.mp this

end Math

