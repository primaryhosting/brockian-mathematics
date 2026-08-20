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

theorem C9adj_mulVec_fourier (k : Fin 9) :
    C9adj *ᵥ (fun i : Fin 9 => (omega9 ^ (k : ℕ)) ^ (i : ℕ)) =
      ((C9eigenvalue k : ℝ) : ℂ) • (fun i : Fin 9 => (omega9 ^ (k : ℕ)) ^ (i : ℕ)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, C9adj, SimpleGraph.adjMatrix_apply, ite_mul,
    one_mul, zero_mul, Pi.smul_apply, smul_eq_mul, ← omega9_add_pow_eight]
  rw [adj_sum_pow _ (omega9_pow_pow_nine k) i, mul_comm]

/-- **Hückel theory for C₉ (characteristic polynomial form).**  The characteristic polynomial
of the adjacency matrix of the cycle `C₉` is `∏_{k=0}^{8} (X - 2 cos (2πk/9))`. -/
