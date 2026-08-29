/-
# Fermat Little
Category: Pure Mathematics
Target: Math.fermat_little
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- **Fermat's little theorem**: if `p` is prime and `a : ℤ` is not divisible by `p`,
then `a ^ (p - 1) ≡ 1 [ZMOD p]`. -/
theorem fermat_little {p : ℕ} (hp : Nat.Prime p) (a : ℤ) (ha : ¬ ((p : ℤ) ∣ a)) :
    a ^ (p - 1) ≡ 1 [ZMOD (p : ℤ)] := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have ha' : (a : ZMod p) ≠ 0 := by
    intro h
    exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have h := ZMod.pow_card_sub_one_eq_one ha'
  have : ((a ^ (p - 1) : ℤ) : ZMod p) = ((1 : ℤ) : ZMod p) := by
    push_cast
    simpa using h
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp this

end Math

