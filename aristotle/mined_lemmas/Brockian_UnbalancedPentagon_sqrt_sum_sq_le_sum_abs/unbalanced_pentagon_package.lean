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

theorem unbalanced_pentagon_package :
    (∀ m : Fin 5 → ℝ, (∀ i, 0 < m i) → g5 / rho m ^ 2 ≤ gap m) ∧
    (∀ m : Fin 5 → ℝ, (∀ i, 0 < m i) → gap m = 1 - (Q_isHermitian m).eigenvalues₀ 1) ∧
    Tendsto (fun t : ℕ => ‖Q (avec t) - Qmin‖) atTop (𝓝 0) ∧
    Qmin_isHermitian.eigenvalues₀ = ![1, 1, 0, -1, -1] ∧
    Tendsto (fun t : ℕ => gap (avec t)) atTop (𝓝 0) ∧
    Tendsto (fun t : ℕ => ‖Q (bvec t) - Qmax‖) atTop (𝓝 0) ∧
    Qmax_isHermitian.eigenvalues₀ = ![1, 0, 0, 0, -1] ∧
    Tendsto (fun t : ℕ => gap (bvec t)) atTop (𝓝 1) ∧
    (∀ m : Fin 5 → ℝ, (∀ i, 0 < m i) → gap m < 1) ∧
    (sInf gapSet = 0 ∧ sSup gapSet = 1 ∧ (0:ℝ) ∉ gapSet ∧ (1:ℝ) ∉ gapSet) :=
  ⟨fun _ hm => gap_lower_bound_of_ratio hm,
   fun _ hm => gap_eq_one_sub_eigenvalues₀_one hm,
   Qa_tendsto_Qmin_opNorm,
   Qmin_eigenvalues,
   gap_tendsto_zero,
   Qb_tendsto_Qmax_opNorm,
   Qmax_eigenvalues,
   gap_tendsto_one,
   fun _ hm => gap_lt_one hm,
   gap_sharp_range⟩

end Brockian.UnbalancedPentagon

import Brockian.Fin5

/-!
# Quotient normalized adjacency matrices of an unbalanced pentagon

Let `m : Fin 5 → ℝ` be a vector of (positive) fibre sizes attached to the vertices of the
5-cycle `C₅`.  We set

* `deg m i = m (i-1) + m (i+1)`  (the "combinatorial" degree seen by vertex `i`),
* `wt m i  = m i * deg m i`      (the weighted degree `D i` of vertex `i`),
* `Q m i j = sqrt (m i * m j / (deg m i * deg m j))` on the edges of `C₅`, `0` otherwise.

`Q m` is exactly the normalized adjacency matrix of the weighted 5-cycle whose edge
conductance on `{i, i+1}` is `m i * m (i+1)`: indeed the weighted degree of `i` is
`m i * (m (i-1) + m (i+1)) = wt m i` and
`m i * m j / sqrt (wt m i * wt m j) = sqrt (m i * m j / (deg m i * deg m j))`.

The vector `perron m i = sqrt (wt m i)` is a positive eigenvector of `Q m` for the
eigenvalue `1`; the spectral gap is defined by a Rayleigh quotient on its orthogonal
complement.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix

/-- The degree `d i = m (i-1) + m (i+1)` of vertex `i` in the 5-cycle. -/
