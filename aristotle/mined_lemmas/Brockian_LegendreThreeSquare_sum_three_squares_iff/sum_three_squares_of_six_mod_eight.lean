import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma sum_three_squares_of_six_mod_eight (t : ℕ) (ht : t % 8 = 6) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = t := by
  -- Squarefree-even Q₁ route (see `exists_even_q1_data_six_mod_eight`).
  obtain ⟨s, m, hm_eq, hm_sq⟩ := exists_squarefree_part t
  have hm6 : m % 8 = 6 := _root_.GeometryOfNumbers.squarefree_part_mod_eight_six t s m hm_eq ht
  have hm_pos : 0 < m := by omega
  obtain ⟨q, b, hq_prime, hq1, hnq, hq_mod, hb⟩ :=
    _root_.GeometryOfNumbers.exists_even_q1_data_six_mod_eight m hm6 hm_sq
  obtain ⟨x, y, z, hQ, _hnz, hxy, hybz⟩ :=
    _root_.GeometryOfNumbers.exists_ankeny_representation_q1 m q b hm_pos hq_prime hnq hq1 hq_mod hb
  have hQ' : (q : ℤ) * x ^ 2 + y ^ 2 + (m : ℤ) * z ^ 2 = (m * q : ℤ) := by
    simpa [ankeny_Q1, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hQ
  obtain ⟨u, v, hm_int⟩ :=
    _root_.GeometryOfNumbers.reduction_to_sum_three_squares_q1 (n := m) (q := q) (x := x) (y := y) (z := z)
      hQ' hq_prime hq1 hq_mod hm_sq b hxy hybz hb
  have hm_rep : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = m := by
    refine ⟨x.natAbs, u.natAbs, v.natAbs, ?_⟩
    zify
    simp [sq_abs, hm_int]
  have hs_rep : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = s ^ 2 * m :=
    sum_three_squares_mul_sq s m hm_rep
  rcases hs_rep with ⟨x', y', z', ht_rep⟩
  refine ⟨x', y', z', ?_⟩
  simpa [hm_eq] using ht_rep
  -- (The earlier development path for this case was kept as a long comment; it has been removed.
  -- See git history if you need the explicit Jacobi-symbol bookkeeping derivation.)

/-!
## Legendre “easy direction”

We prove the modular obstruction:
\[
  x^2 + y^2 + z^2 = n \;\Rightarrow\; n \neq 4^a(8k+7).
\]

Two finite-ring facts drive the proof:

- In `ZMod 4`, `1 + y^2 + z^2 ≠ 0` for all `y,z`. (Checked by `decide`.)
  This implies: if `4 ∣ x^2+y^2+z^2` then `x,y,z` are even, hence we can divide the representation by `4`.

- In `ZMod 8`, `x^2 + y^2 + z^2 ≠ 7` for all `x,y,z`. (Checked by `decide`.)
  This rules out the `8k+7` base case after descending.
-/

