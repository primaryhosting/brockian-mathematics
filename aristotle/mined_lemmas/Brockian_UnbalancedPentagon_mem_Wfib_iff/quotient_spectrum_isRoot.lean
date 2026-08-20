import Brockian.UnbalancedPentagon

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Brockian.UnbalancedPentagon.Basic
import Brockian.UnbalancedPentagon.Operators
import Brockian.UnbalancedPentagon.Decomposition
import Brockian.UnbalancedPentagon.Charpoly
import Brockian.UnbalancedPentagon.Symmetry
import Brockian.UnbalancedPentagon.Balanced

/-!
# The unbalanced pentagon: exact quotient spectrum

Blow up each vertex `i` of the 5-cycle into a fibre of `m i > 0` vertices and join two vertices
whenever their fibres are adjacent in `C₅`.  With `L` the normalized Laplacian, `T` the
fibre-constant isometry and `Q` the `5 × 5` quotient matrix, this development contains:

1. `fiber_decomposition` — the orthogonal splitting into fibre-constant vectors `Ufib` (the
   range of `T`) and fibre-sum-zero vectors `Wfib`;
2. `quotient_intertwining` (and `quotient_intertwining_matrix`) — `L ∘ T = T ∘ (I - Q)`;
3. `fiber_kernel_eigenvalue_one` — `L x = x` for `x ∈ Wfib`, and `dim Wfib = (∑ i, m i) - 5`;
4. `quotient_spectrum` — `charpoly L = (X - 1) ^ ((∑ i, m i) - 5) * charpoly (I - Q)`, with the
   derived multiplicity statement `quotient_spectrum_rootMultiplicity` and the eigenvalue
   statement `quotient_spectrum_isRoot`;
5. `d5_invariant_iff_balanced` — `D₅`-invariance of the fibre sizes is equivalent to their being
   constant, together with the induced graph automorphisms `balancedPerm` in the balanced case
   and `balancedPerm_commutes_Lap`;
6. `balanced_specialization` — for `m i = k > 0`, `Q = A(C₅)/2` and `L` has spectrum `0` (once),
   `(5-√5)/4` (twice), `1` with multiplicity `5(k-1)` and `(5+√5)/4` (twice).
-/

import Brockian.UnbalancedPentagon.Operators

/-!
# The orthogonal fibre decomposition

The space `EuclideanSpace ℝ (V m)` splits as the orthogonal direct sum of

* `Ufib m`, the range of the fibre-constant isometry `T` (the fibre-constant vectors), and
* `Wfib m`, the space of vectors whose sum on each fibre vanishes.

We prove `fiber_decomposition` and `fiber_kernel_eigenvalue_one`
(`L` acts as the identity on `Wfib m`, whose dimension is `(∑ i, m i) - 5`).
-/

namespace Brockian.UnbalancedPentagon

open Finset Matrix RealInnerProductSpace

variable {m : Fin 5 → ℕ}

variable (m) in
/-- Matrix of the fibre-sum map. -/

theorem quotient_spectrum_isRoot (hpos : ∀ i, 0 < m i) (mu : ℝ) :
    ((Lap m).charpoly).IsRoot mu
      ↔ (mu = 1 ∧ 5 < ∑ i, m i) ∨ ((1 - Qmat m).charpoly).IsRoot mu := by
  have hk : ((∑ i, m i) - 5 ≠ 0) ↔ 5 < ∑ i, m i := by
    have := five_le_sum hpos; omega
  rw [quotient_spectrum hpos, Polynomial.IsRoot, Polynomial.eval_mul, mul_eq_zero]
  simp only [Polynomial.eval_pow, pow_eq_zero_iff', Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, sub_eq_zero, Polynomial.IsRoot, hk]

end Brockian.UnbalancedPentagon

import Mathlib

/-!
# Unbalanced pentagon (blow-up of `C₅`): basic definitions

We blow up each vertex `i` of the 5-cycle `C₅` into a fibre of `m i` vertices, and join
two vertices whenever their fibres are adjacent in `C₅`.

This file sets up:

* `C5adj`, the adjacency relation of the 5-cycle on `Fin 5`;
* `V m`, the vertex type `Σ i : Fin 5, Fin (m i)`;
* `deg m i = m (i-1) + m (i+1)`, the common degree of the vertices of fibre `i`;
* the normalized adjacency matrix `Nmat m` and the normalized Laplacian `Lap m = 1 - Nmat m`;
* the `5 × 5` quotient matrix `Qmat m`;
* the matrix `Tmat m` of the fibre-constant isometry `T`.

The basic algebraic facts proved here are
`Tmat_transpose_mul_self : (Tmat m)ᵀ * Tmat m = 1` and
`Nmat_eq_Tmat_mul : Nmat m = Tmat m * Qmat m * (Tmat m)ᵀ`.
-/

namespace Brockian.UnbalancedPentagon

open Finset Matrix

/-! ## The cycle `C₅` -/

/-- Adjacency of the 5-cycle on `Fin 5`. -/
