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

theorem C9adj_mul_F9 :
    C9adj * F9 = F9 * Matrix.diagonal (fun k : Fin 9 => ((C9eigenvalue k : ℝ) : ℂ)) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, F9_apply, C9adj,
    SimpleGraph.adjMatrix_apply, ← omega9_add_pow_eight, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact adj_sum_pow _ (omega9_pow_pow_nine k) i

