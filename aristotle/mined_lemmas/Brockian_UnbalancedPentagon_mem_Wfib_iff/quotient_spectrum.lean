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

theorem quotient_spectrum (hpos : ∀ i, 0 < m i) :
    (Lap m).charpoly
      = ((X : ℝ[X]) - 1) ^ ((∑ i, m i) - 5) * (1 - Qmat m).charpoly := by
  set phi : ℝ[X] →+* RatFunc ℝ := algebraMap ℝ[X] (RatFunc ℝ) with hphi
  have hphi_inj : Function.Injective phi := RatFunc.algebraMap_injective ℝ
  set psi : ℝ →+* RatFunc ℝ := phi.comp (Polynomial.C : ℝ →+* ℝ[X]) with hpsi
  set c : RatFunc ℝ := phi ((X : ℝ[X]) - 1) with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    exact fun h => X_sub_one_ne_zero (hphi_inj (by simpa using h))
  have hLc : charmatrix (Lap m) = ((X : ℝ[X]) - 1) • (1 : Matrix (V m) (V m) ℝ[X])
      + (Nmat m).map C := by
    rw [Lap]
    exact charmatrix_one_sub _ (fun u => by simp [Nmat_apply, C5adj_irrefl u.1])
  have hQc : charmatrix (1 - Qmat m) = ((X : ℝ[X]) - 1) • (1 : Matrix (Fin 5) (Fin 5) ℝ[X])
      + (Qmat m).map C :=
    charmatrix_one_sub _ (fun i => by simp [Qmat_apply, C5adj_irrefl i])
  have hmapN : ((Nmat m).map C).map phi
      = ((Tmat m).map psi * (Qmat m).map psi) * (((Tmat m)ᵀ).map psi) := by
    have h0 : ((Nmat m).map C).map phi = (Nmat m).map psi := by
      ext u v; simp [hpsi]
    rw [h0, Nmat_eq_Tmat_mul hpos, ← Matrix.map_mul, ← Matrix.map_mul]
  have hmapQ : ((Qmat m).map C).map phi = (Qmat m).map psi := by
    ext i j; simp [hpsi]
  have hBA : (((Tmat m)ᵀ).map psi) * ((Tmat m).map psi * (Qmat m).map psi)
      = (Qmat m).map psi := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, Tmat_transpose_mul_self hpos,
      Matrix.map_one _ (map_zero psi) (map_one psi), Matrix.one_mul]
  have e1 : phi ((Lap m).charpoly) = ((charmatrix (Lap m)).map phi).det := by
    rw [Matrix.charpoly, RingHom.map_det]; rfl
  have e2 : phi ((1 - Qmat m).charpoly) = ((charmatrix (1 - Qmat m)).map phi).det := by
    rw [Matrix.charpoly, RingHom.map_det]; rfl
  refine hphi_inj ?_
  rw [map_mul, e1, e2, hLc, hQc, map_smul_one_add, map_smul_one_add, hmapN, hmapQ, ← hc,
    det_smul_one_add_mul_comm c hcne _ _ (by simpa using five_le_card_V hpos), hBA]
  congr 1
  rw [map_pow, ← hc, card_V]
  simp

/-! ## Multiplicities and eigenvalues -/

