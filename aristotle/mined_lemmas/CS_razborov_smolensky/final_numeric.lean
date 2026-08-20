import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem final_numeric {m D Mid : ℕ} (hMid : 1 ≤ Mid) (hMid2 : Mid ^ 2 * (3 * m + 1) ≤ 16 ^ m)
    (hD : 64 * (D + 1) ^ 2 ≤ 27 * m) : 8 * ((D + 1) * Mid) < 3 * 4 ^ m := by
  have hsq : (8 * ((D + 1) * Mid)) ^ 2 < (3 * 4 ^ m) ^ 2 := by
    have h2 : (3 * 4 ^ m) ^ 2 = 9 * 16 ^ m := by
      rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul]
      norm_num
    calc (8 * ((D + 1) * Mid)) ^ 2 = 64 * (D + 1) ^ 2 * Mid ^ 2 := by ring
      _ ≤ 27 * m * Mid ^ 2 := Nat.mul_le_mul_right _ hD
      _ < 9 * (Mid ^ 2 * (3 * m + 1)) := by nlinarith [Nat.one_le_iff_ne_zero.mp hMid]
      _ ≤ 9 * 16 ^ m := Nat.mul_le_mul_left _ hMid2
      _ = (3 * 4 ^ m) ^ 2 := h2.symm
  exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp hsq

end CS

import RequestProject.Deg
import RequestProject.Aux

/-!
# Approximating an `OR` gate by a low degree polynomial

The key probabilistic step of Razborov–Smolensky: an unbounded fan-in `OR` of functions that
are already approximated by degree `Dc` polynomials over a field of characteristic `q` is
approximated by a polynomial of degree `t (q-1) Dc`, with an additional error on at most a
`2⁻ᵗ` fraction of the cube.
-/

namespace CS

open Finset

variable {F : Type*} [Field F] {q : ℕ} [hq : Fact q.Prime] [CharP F q]

