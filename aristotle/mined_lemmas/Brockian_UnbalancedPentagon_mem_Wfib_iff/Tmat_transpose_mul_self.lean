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

lemma Tmat_transpose_mul_self (hpos : ∀ i, 0 < m i) : (Tmat m)ᵀ * Tmat m = 1 := by
  ext i j
  rw [Matrix.mul_apply, sum_V]
  simp only [Matrix.transpose_apply, Tmat_apply]
  have hconst : ∀ k : Fin 5, ∑ _a : Fin (m k),
      ((if k = i then 1 / Real.sqrt (m i) else 0) * (if k = j then 1 / Real.sqrt (m j) else 0))
      = (m k : ℝ) * ((if k = i then 1 / Real.sqrt (m i) else 0)
          * (if k = j then 1 / Real.sqrt (m j) else 0)) := by
    intro k; simp [Finset.sum_const, mul_comm]
  simp only [hconst]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · have h1 : Real.sqrt (m i) * Real.sqrt (m i) = m i :=
        Real.mul_self_sqrt (le_of_lt (m_pos_real hpos i))
      rw [Matrix.one_apply_eq]
      simp only [if_true]
      rw [one_div, ← mul_inv, h1]
      exact mul_inv_cancel₀ (ne_of_gt (m_pos_real hpos i))
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [Matrix.one_apply_ne hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : k = i
    · subst h1; simp [hij]
    · simp [h1]

/-- Multiplying a `5 × 5` matrix on the left by `T`. -/
