import Brockian.Fin5
import Brockian.Defs
import Brockian.Rayleigh
import Brockian.Gap
import Brockian.Poincare
import Brockian.LowerBound
import Brockian.LtOne
import Brockian.Perturb
import Brockian.LimitMatrices
import Brockian.FamilyDefs
import Brockian.LimitA
import Brockian.LimitB
import Brockian.GapLimits
import Brockian.Range
import Brockian.Spectrum
import Brockian.OpNorm
import Brockian.MinMax
import Brockian.UnbalancedPentagonLimits

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

import Brockian.LimitA
import Brockian.LimitB
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator-norm form of the two matrix limits

The entrywise `ℓ¹` norm `nrm1` dominates the `ℓ²` operator norm of a `5 × 5` real matrix
(`opNorm_le_nrm1`).  Consequently the entrywise convergences `Qa_tendsto_Qmin` and
`Qb_tendsto_Qmax` upgrade to convergence in the operator norm.
-/

namespace Brockian.UnbalancedPentagon

open Matrix Finset Filter Topology
open scoped Matrix.Norms.L2Operator

/-- `√(∑ |wᵢ|²) ≤ ∑ |wᵢ|`. -/

theorem eigenvalues₀_eq_of_charpoly (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.IsHermitian)
    (μ : Fin 5 → ℝ) (hμ : Antitone μ)
    (hc : A.charpoly = ∏ i, (X - C (μ i))) : hA.eigenvalues₀ = μ := by
  have hroots : A.charpoly.roots = Multiset.map μ Finset.univ.val := by
    rw [hc, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsort := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots] at hsort
  have h2 : (Multiset.map (RCLike.re : ℝ → ℝ) (Multiset.map μ Finset.univ.val)).sort (· ≥ ·)
      = List.ofFn μ := by
    rw [Multiset.map_map]
    simp only [Function.comp_def, RCLike.re_to_real]
    rw [Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hμ.sortedGE_ofFn
  rw [h2] at hsort
  exact List.ofFn_injective hsort.symm

/-! ### `Qmin` -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
/-- The characteristic polynomial of `Qmin` is `(X-1)²X(X+1)²`. -/
