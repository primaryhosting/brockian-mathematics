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

theorem fiber_kernel_eigenvalue_one (hpos : ∀ i, 0 < m i) :
    (∀ x ∈ Wfib m, Lop m x = x) ∧
      Module.finrank ℝ (Wfib m) = (∑ i, m i) - 5 := by
  constructor
  · intro x hx
    have hN := Nop_eq_zero_on_Wfib x hx
    have : Lop m x = Matrix.toEuclideanLin (1 : Matrix (V m) (V m) ℝ) x
        - Matrix.toEuclideanLin (Nmat m) x := by
      rw [Lop, Lap, map_sub]
      rfl
    rw [this, hN, sub_zero]
    ext u
    rw [toEuclideanLin_apply', Finset.sum_eq_single u]
    · rw [Matrix.one_apply_eq, one_mul]
    · intro b _ hb; rw [Matrix.one_apply_ne (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ u) h
  · have hrange : LinearMap.range (fibreSum m) = ⊤ := by
      rw [eq_top_iff]
      rintro f -
      refine ⟨Tlin m (WithLp.toLp 2 fun i => f i * Real.sqrt (m i) / m i), ?_⟩
      ext i
      rw [fibreSum_apply]
      have : ∀ a : Fin (m i),
          Tlin m (WithLp.toLp 2 fun i => f i * Real.sqrt (m i) / m i) ⟨i, a⟩
            = f i / (m i : ℝ) := by
        intro a
        rw [Tlin_apply]
        have h1 := sqrt_m_ne hpos i
        have h2 := ne_of_gt (m_pos_real hpos i)
        field_simp
      rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_comm,
        div_mul_cancel₀ _ (ne_of_gt (m_pos_real hpos i))]
    have hrk : Module.finrank ℝ (LinearMap.range (fibreSum m))
        + Module.finrank ℝ (LinearMap.ker (fibreSum m))
        = Module.finrank ℝ (EuclideanSpace ℝ (V m)) :=
      LinearMap.finrank_range_add_finrank_ker _
    rw [hrange] at hrk
    have h5 : Module.finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 5))) = 5 := by
      rw [finrank_top, finrank_euclideanSpace, Fintype.card_fin]
    have hn : Module.finrank ℝ (EuclideanSpace ℝ (V m)) = ∑ i, m i := by
      rw [finrank_euclideanSpace, card_V]
    rw [h5, hn] at hrk
    rw [Wfib]
    omega

end Brockian.UnbalancedPentagon

import Brockian.UnbalancedPentagon.Charpoly

/-!
# The balanced specialization

For `m i = k > 0` the quotient matrix is `Q = A(C₅) / 2` and the normalized Laplacian has the
classical spectrum

* `0` with multiplicity `1`,
* `(5 - √5) / 4` with multiplicity `2`,
* `1` with multiplicity `5 (k - 1)`,
* `(5 + √5) / 4` with multiplicity `2`.
-/

namespace Brockian.UnbalancedPentagon

open Finset Matrix Polynomial

/-- The adjacency matrix of the 5-cycle. -/
