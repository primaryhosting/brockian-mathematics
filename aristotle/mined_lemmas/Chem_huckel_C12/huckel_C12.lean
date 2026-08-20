import Mathlib

/-!
# Hückel spectrum of the cycle graph `C₁₂`

We show that the eigenvalues (i.e. the spectrum) of the adjacency matrix of the cycle graph
`C₁₂`, viewed as a complex matrix indexed by `ZMod 12`, are exactly the numbers
`2 * cos (2 * π * k / 12)` for `k = 0, …, 11`.

The proof goes through the cyclic shift matrix `S` on `ZMod 12`: the adjacency matrix is
`S + S ^ 11`, the spectrum of `S` is the set of `12`-th roots of unity, and the polynomial
spectral mapping theorem over `ℂ` transports this to the adjacency matrix.
-/

namespace Chem

open Matrix Polynomial

/-- The cyclic shift matrix on `ZMod 12`. -/

theorem huckel_C12 :
    spectrum ℂ C12adj
      = Set.range (fun k : Fin 12 => ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ)) := by
  have hp : C12adj = aeval shift12 (X + X ^ 11 : ℂ[X]) := by
    simp [C12adj_eq]
  have hdeg : (0 : WithBot ℕ) < (X + X ^ 11 : ℂ[X]).degree := by
    have h : (X + X ^ 11 : ℂ[X]).degree = 11 := by compute_degree!
    rw [h]; norm_num
  rw [hp, spectrum.map_polynomial_aeval_of_degree_pos _ _ hdeg,
    spectrum_shift12, rootsOfUnity12, ← Set.range_comp]
  apply congrArg Set.range
  funext k
  simpa only [Function.comp_apply, eval_add, eval_pow, eval_X] using exp_add_pow_eleven (k : ℕ)

/-- The same statement phrased with Mathlib's cycle graph `SimpleGraph.cycleGraph 12`. -/
