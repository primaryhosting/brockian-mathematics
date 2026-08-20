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

lemma centralBinom_sq_mul_le (m : ℕ) :
    (Nat.centralBinom m) ^ 2 * (3 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp [Nat.centralBinom]
  | succ m ih =>
      have hid : (m + 1) * Nat.centralBinom (m + 1) = 2 * (2 * m + 1) * Nat.centralBinom m :=
        Nat.succ_mul_centralBinom_succ m
      set A := Nat.centralBinom m with hA
      set B := Nat.centralBinom (m + 1) with hB
      have hsq : ((m + 1) * B) ^ 2 = 4 * (2 * m + 1) ^ 2 * A ^ 2 := by
        rw [hid]; ring
      -- the key polynomial inequality
      have hpoly : 4 * (2 * m + 1) ^ 2 * (3 * (m + 1) + 1) ≤ 16 * (m + 1) ^ 2 * (3 * m + 1) := by
        nlinarith [sq_nonneg m, Nat.zero_le m]
      have hstep : ((m + 1) ^ 2) * (B ^ 2 * (3 * (m + 1) + 1))
          ≤ ((m + 1) ^ 2) * (16 ^ (m + 1)) := by
        calc ((m + 1) ^ 2) * (B ^ 2 * (3 * (m + 1) + 1))
            = ((m + 1) * B) ^ 2 * (3 * (m + 1) + 1) := by ring
          _ = (4 * (2 * m + 1) ^ 2 * (3 * (m + 1) + 1)) * A ^ 2 := by rw [hsq]; ring
          _ ≤ (16 * (m + 1) ^ 2 * (3 * m + 1)) * A ^ 2 := Nat.mul_le_mul_right _ hpoly
          _ = (16 * (m + 1) ^ 2) * (A ^ 2 * (3 * m + 1)) := by ring
          _ ≤ (16 * (m + 1) ^ 2) * 16 ^ m := Nat.mul_le_mul_left _ ih
          _ = ((m + 1) ^ 2) * (16 ^ (m + 1)) := by ring
      exact Nat.le_of_mul_le_mul_left hstep (by positivity)

/-- The number of subsets of size at most `K` of an `N`-element set. -/
