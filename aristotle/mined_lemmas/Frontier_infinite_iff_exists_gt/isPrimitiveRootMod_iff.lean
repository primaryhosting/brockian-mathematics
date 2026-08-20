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
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is repeated below as a module docstring; Lean 4 does not allow a module
-- docstring to precede the `import` line.)
import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo the prime `p` when the residue of `a` generates the
multiplicative group of `ZMod p`, i.e. its multiplicative order is exactly `p - 1`. -/

theorem isPrimitiveRootMod_iff {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    IsPrimitiveRootMod a p ↔
      ∀ q : ℕ, q.Prime → q ∣ (p - 1) → ((a : ZMod p)) ^ ((p - 1) / q) ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  constructor
  · intro h q hq hdvd hpow
    have hdvd' : orderOf ((a : ZMod p)) ∣ (p - 1) / q := orderOf_dvd_of_pow_eq_one hpow
    rw [show orderOf ((a : ZMod p)) = p - 1 from h] at hdvd'
    have hlt : (p - 1) / q < p - 1 := Nat.div_lt_self hp1 hq.one_lt
    have hpos : 0 < (p - 1) / q := Nat.div_pos (Nat.le_of_dvd hp1 hdvd) hq.pos
    exact absurd (Nat.le_of_dvd hpos hdvd') (by omega)
  · intro h
    exact orderOf_eq_of_pow_and_pow_div_prime hp1 (ZMod.pow_card_sub_one_eq_one ha) h

/-! ### The hypotheses of Artin's conjecture are necessary -/

/-- If `a` is a perfect square then it is a primitive root modulo no odd prime; hence the only
possible member of `artinSet a` is `2`. -/
