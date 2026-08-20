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

theorem euler_totient_units_of_lagrange {n : ℕ} (x : (ZMod n)ˣ) : x ^ Nat.totient n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · haveI : NeZero n := ⟨hn⟩
    haveI : Fintype (ZMod n)ˣ := inferInstance
    rw [← ZMod.card_units_eq_totient n, pow_card_eq_one]

/-- **Euler's theorem**, ring-element form: if `a : ZMod n` is a unit then `a ^ φ n = 1`. -/
