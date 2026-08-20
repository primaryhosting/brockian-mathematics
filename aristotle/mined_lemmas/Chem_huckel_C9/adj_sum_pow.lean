import Mathlib

/-!
# Hückel theory for the cycle C₉

The adjacency matrix of the cycle graph `C₉` is diagonalized by the discrete Fourier
(Vandermonde) matrix built from a primitive 9-th root of unity.  Consequently its
characteristic polynomial factors as `∏ k, (X - 2 cos (2πk/9))`, and its spectrum is
exactly `{2 cos (2πk/9) : k = 0, …, 8}` — the Hückel energy levels of a nine-membered
conjugated ring.
-/

open Polynomial Matrix SimpleGraph Complex

namespace Chem

/-- The adjacency matrix of the cycle graph `C₉`, over `ℂ`. -/

theorem adj_sum_pow (x : ℂ) (hx9 : x ^ 9 = 1) (i : Fin 9) :
    (∑ j : Fin 9, (if (cycleGraph 9).Adj i j then x ^ (j : ℕ) else 0)) = x ^ (i : ℕ) * (x + x ^ 8) := by
  fin_cases i <;> simp +decide [Fin.sum_univ_succ]
  · linear_combination -hx9
  · linear_combination (-x) * hx9
  · linear_combination (-x ^ 2) * hx9
  · linear_combination (-x ^ 3) * hx9
  · linear_combination (-x ^ 4) * hx9
  · linear_combination (-x ^ 5) * hx9
  · linear_combination (-x ^ 6) * hx9
  · linear_combination (-(1 + x ^ 7)) * hx9

/-- `ω^k + ω^{-k} = 2 cos (2πk/9)`. -/
