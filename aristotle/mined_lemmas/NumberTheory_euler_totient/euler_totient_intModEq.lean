/-
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the first command in a file, so the
required header block appears twice: verbatim as a plain comment at the very top of the
file, and again as the module docstring immediately after the import.
-/

namespace NumberTheory

/-!
## Euler's theorem

The main statement is `NumberTheory.euler_totient`: if `a : ZMod n` is a unit, then
`a ^ Nat.totient n = 1`.

We give two routes to the underlying unit-group statement:

* `euler_totient_units`, which cites Mathlib's `ZMod.pow_totient`;
* `euler_totient_units_of_lagrange`, a short proof from the group-theoretic machinery
  (`pow_card_eq_one`, i.e. Lagrange's theorem, together with
  `ZMod.card_units_eq_totient : Fintype.card (ZMod n)ˣ = n.totient`).

We also record the two classical congruence formulations, over `ℕ` and over `ℤ`.
-/

/-- **Euler's theorem**, unit-group form: for a unit `x` of `ZMod n`, `x ^ φ n = 1`.

This is Mathlib's `ZMod.pow_totient`. -/

theorem euler_totient_intModEq {a : ℤ} {n : ℕ} (h : IsCoprime a (n : ℤ)) :
    a ^ Nat.totient n ≡ 1 [ZMOD (n : ℤ)] := by
  have hu : IsUnit ((a : ZMod n)) := by
    have := h.map (Int.castRingHom (ZMod n))
    simpa [isCoprime_zero_right] using this
  have hcast : ((a ^ Nat.totient n : ℤ) : ZMod n) = ((1 : ℤ) : ZMod n) := by
    push_cast
    exact euler_totient hu
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hcast

end NumberTheory

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

