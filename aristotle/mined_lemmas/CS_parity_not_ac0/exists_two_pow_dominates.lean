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

lemma exists_two_pow_dominates (A K B : ℕ) : ∃ i : ℕ, B * (A * (i + 2)) ^ K ≤ 2 ^ i := by
  set k := 3 * K + 3 with hk
  refine ⟨max (max A B) (max 2 (k * (k + k ^ 2 + 1))), ?_⟩
  set i := max (max A B) (max 2 (k * (k + k ^ 2 + 1))) with hi
  have hiA : A ≤ i := le_trans (le_max_left _ _) (le_max_left _ _)
  have hiB : B ≤ i := le_trans (le_max_right _ _) (le_max_left _ _)
  have hi2 : 2 ≤ i := le_trans (le_max_left _ _) (le_max_right _ _)
  have hik : k * (k + k ^ 2 + 1) ≤ i := le_trans (le_max_right _ _) (le_max_right _ _)
  have hB3 : B ≤ i ^ 3 := le_trans hiB (Nat.le_self_pow (by norm_num) i)
  have hA3 : A * (i + 2) ≤ i ^ 3 := by
    have h1 : A * (i + 2) ≤ i * (i + 2) := Nat.mul_le_mul_right _ hiA
    have h2 : i * (i + 2) ≤ i * (2 * i) := Nat.mul_le_mul_left _ (by omega)
    have h3 : i * (2 * i) ≤ i * (i * i) := Nat.mul_le_mul_left _ (by nlinarith)
    calc A * (i + 2) ≤ i * (i * i) := by omega
      _ = i ^ 3 := by ring
  calc B * (A * (i + 2)) ^ K ≤ i ^ 3 * (i ^ 3) ^ K :=
        Nat.mul_le_mul hB3 (Nat.pow_le_pow_left hA3 K)
    _ = i ^ (3 * K + 3) := by rw [← pow_mul, ← pow_add]; ring_nf
    _ = i ^ k := by rw [hk]
    _ ≤ 2 ^ i := pow_le_two_pow hik

end CS

import RequestProject.Circuit

/-!
# Smolensky's degree lower bound for parity

If a function `g` of degree at most `D` (over `ZMod 3`, in the `±1` encoding)
agrees with `PARITY` on a set `G` of inputs, then `G` cannot be large:
`|G| ≤ #{T ⊆ [n] : |T| ≤ K}` whenever `n + D ≤ 2K`.

The argument is Smolensky's: on the agreement set every monomial of high degree
can be traded, using `g`, for one of degree at most `K`; since the point
indicators span all functions on `G`, the restrictions of the monomials of degree
at most `K` span the whole `|G|`-dimensional space of functions on `G`.
-/

namespace CS

open Finset

/-- The indicator function of a point of the cube, as a product of linear factors. -/
