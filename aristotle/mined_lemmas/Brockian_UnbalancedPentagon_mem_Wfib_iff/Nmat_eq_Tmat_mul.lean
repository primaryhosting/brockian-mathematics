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

lemma Nmat_eq_Tmat_mul (hpos : ∀ i, 0 < m i) : Nmat m = Tmat m * Qmat m * (Tmat m)ᵀ := by
  ext u v
  rw [mul_Tmat_transpose_apply, Tmat_mul_apply, Nmat_apply, Qmat_apply]
  by_cases h : C5adj u.1 v.1
  · simp only [if_pos h]
    rw [sqrt_mul_div_mul (le_of_lt (m_pos_real hpos u.1)) (le_of_lt (m_pos_real hpos v.1))
      (le_of_lt (deg_pos_real hpos u.1))]
    have h1 := sqrt_m_ne hpos u.1
    have h2 := sqrt_m_ne hpos v.1
    have h3 := sqrt_deg_ne hpos u.1
    have h4 := sqrt_deg_ne hpos v.1
    field_simp
  · simp [h]

end Brockian.UnbalancedPentagon

import Brockian.UnbalancedPentagon

/-!
# Axiom audit

Building this module prints the axiom dependencies of every public target of
`Brockian.UnbalancedPentagon`.  All of them use only `propext`, `Classical.choice` and
`Quot.sound`.
-/

#print axioms Brockian.UnbalancedPentagon.fiber_decomposition
#print axioms Brockian.UnbalancedPentagon.quotient_intertwining
#print axioms Brockian.UnbalancedPentagon.quotient_intertwining_matrix
#print axioms Brockian.UnbalancedPentagon.fiber_kernel_eigenvalue_one
#print axioms Brockian.UnbalancedPentagon.quotient_spectrum
#print axioms Brockian.UnbalancedPentagon.quotient_spectrum_rootMultiplicity
#print axioms Brockian.UnbalancedPentagon.quotient_spectrum_isRoot
#print axioms Brockian.UnbalancedPentagon.isRoot_charpoly_iff
#print axioms Brockian.UnbalancedPentagon.d5_invariant_iff_balanced
#print axioms Brockian.UnbalancedPentagon.balancedPerm_isAutomorphism
#print axioms Brockian.UnbalancedPentagon.balancedPerm_commutes_Lap
#print axioms Brockian.UnbalancedPentagon.balanced_specialization
#print axioms Brockian.UnbalancedPentagon.Qmat_balanced
#print axioms Brockian.UnbalancedPentagon.charpoly_Lap_balanced
#print axioms Brockian.UnbalancedPentagon.balanced_rootMultiplicity

import Brockian.UnbalancedPentagon.Basic

/-!
# The dihedral symmetry `D₅`

The dihedral group of order 10 acts on `Fin 5` by rotations `i ↦ i + c` and reflections
`i ↦ c - i`. We show:

* `d5_invariant_iff_balanced`: a fibre-size function `m` is invariant under the whole `D₅`
  action iff it is constant;
* in the constant (balanced) case there *is* a canonical induced action on the vertex type
  `V (fun _ => k)`, given by `balancedPerm`, and these vertex permutations are graph
  automorphisms which commute with the normalized Laplacian (`balancedPerm_commutes_Lap`).

Note that for a genuinely unbalanced `m` there is no base-only action on the dependent vertex
type `Σ i, Fin (m i)`: a rotation would have to map a fibre of size `m i` to a fibre of a
different size.
-/

namespace Brockian.UnbalancedPentagon

open Finset Matrix

/-! ## The `D₅` action on `Fin 5` -/

/-- The rotation `i ↦ i + c` of the pentagon. -/
