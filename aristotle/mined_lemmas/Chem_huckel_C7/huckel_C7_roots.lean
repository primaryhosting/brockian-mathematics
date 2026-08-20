/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Hückel theory for the cycle `C₇`

In Hückel molecular orbital theory the (reduced) Hamiltonian of a conjugated
cyclic polyene `Cₙ` is the adjacency matrix of the cycle graph `Cₙ`, and the
orbital energies are `α + β λ` where `λ` runs over the adjacency eigenvalues.
For `n = 7` (the cycloheptatrienyl system) the eigenvalues are
`2 cos (2πk/7)`, `k = 0, …, 6`.

The proof diagonalises the adjacency matrix by the discrete Fourier
(Vandermonde) matrix built from `ω = exp (2πi/7)`.
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The primitive 7-th root of unity `ω = exp (2πi/7)`. -/

theorem huckel_C7_roots :
    {μ : ℂ | ((cycleGraph 7).adjMatrix ℂ).charpoly.IsRoot μ}
      = Set.range (fun k : Fin 7 => ((2 * Real.cos (2 * Real.pi * k / 7) : ℝ) : ℂ)) := by
  ext μ
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot, huckel_C7, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero, Set.mem_range]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩

end Chem

