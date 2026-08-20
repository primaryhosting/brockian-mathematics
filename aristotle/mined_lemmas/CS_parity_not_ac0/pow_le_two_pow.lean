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

lemma pow_le_two_pow {k i : ℕ} (h : k * (k + k ^ 2 + 1) ≤ i) : i ^ k ≤ 2 ^ i := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simpa using Nat.one_le_two_pow
  set q := i / k with hq
  have hik : i = k * q + i % k := (Nat.div_add_mod i k).symm
  have hmod : i % k < k := Nat.mod_lt _ hk
  have hqge : k ^ 2 + k ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le hk]
    nlinarith
  have hilt : i ≤ k * (q + 1) := by nlinarith
  have hkey : k * (q + 1) ≤ 2 ^ q := linear_le_two_pow hqge
  calc i ^ k ≤ (2 ^ q) ^ k := Nat.pow_le_pow_left (le_trans hilt hkey) k
    _ = 2 ^ (q * k) := by rw [← pow_mul]
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm q k]; omega)

/-- Exponentials dominate polynomials: `B * (A * (i+2))^K ≤ 2^i` for some `i`. -/
