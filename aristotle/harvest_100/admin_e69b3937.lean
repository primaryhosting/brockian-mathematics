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

/-- **Fermat's little theorem.** If `p` is prime and the integer `a` is not divisible by `p`,
then `a ^ (p - 1) ≡ 1 (mod p)`. -/
theorem fermat_little {p : ℕ} (hp : Nat.Prime p) {a : ℤ} (ha : ¬ ((p : ℤ) ∣ a)) :
    a ^ (p - 1) ≡ 1 [ZMOD (p : ℤ)] := by
  haveI : Fact (Nat.Prime p) := Fact.mk hp
  have h0 : ((a : ZMod p)) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using ha
  have hpow : ((a : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h0
  have h2 : ((a ^ (p - 1) : ℤ) : ZMod p) = ((1 : ℤ) : ZMod p) := by
    push_cast
    simpa using hpow
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp h2

/-- Natural-number form of Fermat's little theorem. -/
theorem fermat_little_nat {p a : ℕ} (hp : Nat.Prime p) (ha : ¬ (p ∣ a)) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have ha' : ¬ ((p : ℤ) ∣ (a : ℤ)) := by
    simpa [Int.natCast_dvd_natCast] using ha
  have := fermat_little hp ha'
  have h : ((a ^ (p - 1) : ℕ) : ℤ) ≡ ((1 : ℕ) : ℤ) [ZMOD (p : ℤ)] := by
    push_cast
    simpa using this
  exact Int.natCast_modEq_iff.mp h

end Math

