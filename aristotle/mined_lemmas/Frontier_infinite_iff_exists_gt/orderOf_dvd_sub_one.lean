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

theorem orderOf_dvd_sub_one {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    orderOf ((a : ZMod p)) ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one ha)

/-- **Lucas-type criterion / reduction.** For a prime `p` not dividing `a`, the integer `a` is a
primitive root mod `p` exactly when `a ^ ((p-1)/q) ≢ 1` for every prime `q` dividing `p - 1`.
This reduces membership in `artinSet a` to a finite computation. -/
