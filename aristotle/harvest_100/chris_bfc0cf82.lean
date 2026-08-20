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
theorem euler_totient_units {n : ℕ} (x : (ZMod n)ˣ) : x ^ Nat.totient n = 1 :=
  ZMod.pow_totient x

/-- **Euler's theorem**, unit-group form, proved from Lagrange's theorem instead of
citing `ZMod.pow_totient`: the group `(ZMod n)ˣ` has order `φ n`, so every element is
killed by the `φ n`-th power. The degenerate case `n = 0` is handled separately, since
`(ZMod 0)ˣ = ℤˣ` is finite but `φ 0 = 0`, making the statement trivial there. -/
theorem euler_totient_units_of_lagrange {n : ℕ} (x : (ZMod n)ˣ) : x ^ Nat.totient n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · haveI : NeZero n := ⟨hn⟩
    haveI : Fintype (ZMod n)ˣ := inferInstance
    rw [← ZMod.card_units_eq_totient n, pow_card_eq_one]

/-- **Euler's theorem**, ring-element form: if `a : ZMod n` is a unit then `a ^ φ n = 1`. -/
theorem euler_totient {n : ℕ} {a : ZMod n} (ha : IsUnit a) : a ^ Nat.totient n = 1 := by
  obtain ⟨u, rfl⟩ := ha
  rw [← Units.val_pow_eq_pow_val, euler_totient_units_of_lagrange u, Units.val_one]

/-- **Euler's theorem**, congruence form over `ℕ`: if `a` and `n` are coprime natural
numbers, then `a ^ φ n ≡ 1 [MOD n]`.

This is Mathlib's `Nat.ModEq.pow_totient`. -/
theorem euler_totient_modEq {a n : ℕ} (h : Nat.Coprime a n) :
    a ^ Nat.totient n ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

/-- **Euler's theorem**, congruence form over `ℤ`: if `a : ℤ` is coprime to `n`, then
`a ^ φ n ≡ 1 [ZMOD n]`.

Proof: coprimality is preserved by the ring map `ℤ → ZMod n`, under which `n ↦ 0`, so
`(a : ZMod n)` is coprime to `0`, i.e. a unit; now apply `euler_totient`. -/
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

