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

namespace Math

/-- **Fermat's little theorem**: if `p` is prime and `p ∤ a`, then
`a ^ (p - 1) ≡ 1 (mod p)`.

The proof reduces to `ZMod.pow_card_sub_one_eq_one` in Mathlib (the statement in the
finite field `ZMod p`), transferred back to `Int.ModEq` via `ZMod.intCast_eq_intCast_iff'`. -/
theorem fermat_little {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    a ^ (p - 1) ≡ 1 [ZMOD (p : ℤ)] := by
  haveI := Fact.mk hp
  have h0 : ((a : ZMod p)) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using ha
  have h := ZMod.pow_card_sub_one_eq_one h0
  have hc : ((a ^ (p - 1) : ℤ) : ZMod p) = ((1 : ℤ) : ZMod p) := by
    push_cast; simpa using h
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp (by simpa using hc)

/-- Natural-number form of Fermat's little theorem. -/
theorem fermat_little_nat {p a : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have h := fermat_little hp (a := (a : ℤ)) (by exact_mod_cast ha)
  exact Int.natCast_modEq_iff.mp (by push_cast; simpa using h)

end Math

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

