import RequestProject.Basic

/-!
# Unbounded fan-in Boolean circuits, the class `AC⁰`, and `PARITY`

A `Circuit n` is a Boolean circuit on `n` inputs built from constants, input
variables, negations, and *unbounded fan-in* `AND`/`OR` gates.

* `Circuit.depth` counts the maximal number of `AND`/`OR` gates on a root-to-leaf
  path (negations are free, as is standard for `AC⁰`).
* `Circuit.size` counts the number of `AND`/`OR` gates.

`InAC0 f` says that the family `f` is computed by circuits of some fixed depth and
polynomial size.  Making negations free and not counting them in the size only
makes the class larger, hence the lower bound proved later stronger.
-/

namespace CS

/-- Boolean circuits with unbounded fan-in `AND`/`OR` gates. -/
inductive Circuit (n : ℕ) where
  | const : Bool → Circuit n
  | var : Fin n → Circuit n
  | neg : Circuit n → Circuit n
  | or : (m : ℕ) → (Fin m → Circuit n) → Circuit n
  | and : (m : ℕ) → (Fin m → Circuit n) → Circuit n

namespace Circuit

/-- The Boolean function computed by a circuit. -/

lemma linear_le_two_pow {k q : ℕ} (h : k ^ 2 + k ≤ q) : k * (q + 1) ≤ 2 ^ q := by
  obtain ⟨r, rfl⟩ : ∃ r, q = k + r := ⟨q - k, by omega⟩
  have hr : k ^ 2 ≤ r + 1 := by nlinarith
  have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h2 : r + 1 ≤ 2 ^ r := Nat.lt_two_pow_self
  calc k * (k + r + 1) ≤ (k + 1) * (r + 1) := by nlinarith
    _ ≤ 2 ^ k * 2 ^ r := Nat.mul_le_mul h1 h2
    _ = 2 ^ (k + r) := by rw [← pow_add]

/-- Polynomials are dominated by the exponential: `i^k ≤ 2^i` for `i` large. -/
