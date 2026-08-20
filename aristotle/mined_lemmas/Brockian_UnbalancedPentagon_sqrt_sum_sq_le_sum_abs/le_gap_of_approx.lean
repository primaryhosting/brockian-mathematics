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

theorem le_gap_of_approx (hm : ∀ i, 0 < m i) {B : Matrix (Fin 5) (Fin 5) ℝ} (z z' : Fin 5 → ℝ)
    (c : ℝ) (hB : ∀ x : Fin 5 → ℝ, x ⬝ᵥ (B *ᵥ x) = (z ⬝ᵥ x) ^ 2 - (z' ⬝ᵥ x) ^ 2) :
    1 - (∑ i, (z i - c * perron m i) ^ 2) - nrm1 (Q m - B) ≤ gap m := by
  have hsec : sec (Q m) (perron m) ≤ (∑ i, (z i - c * perron m i) ^ 2) + nrm1 (Q m - B) := by
    refine sec_le_of hm ?_
    intro x hx hp
    have e1 : x ⬝ᵥ (Q m *ᵥ x) = x ⬝ᵥ (B *ᵥ x) + x ⬝ᵥ ((Q m - B) *ᵥ x) := by
      rw [sub_mulVec, dotProduct_sub]; ring
    have e2 : x ⬝ᵥ (B *ᵥ x) ≤ (z ⬝ᵥ x) ^ 2 := by
      rw [hB x]; nlinarith [sq_nonneg (z' ⬝ᵥ x)]
    have hzx : z ⬝ᵥ x = (fun i => z i - c * perron m i) ⬝ᵥ x := by
      simp only [dotProduct, sub_mul, Finset.sum_sub_distrib]
      have : ∑ i, c * perron m i * x i = c * (perron m ⬝ᵥ x) := by
        rw [dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, hp, mul_zero, sub_zero]
    have e3 : (z ⬝ᵥ x) ^ 2 ≤ ∑ i, (z i - c * perron m i) ^ 2 := by
      rw [hzx]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i => z i - c * perron m i) (fun i => x i)
      have hxx : ∑ i, (x i) ^ 2 = 1 := by rw [← dotProduct_self_eq_sum_sq]; exact hx
      rw [hxx, mul_one] at hcs
      simpa [dotProduct] using hcs
    have e4 := abs_le.mp (abs_dot_mulVec_le (Q m - B) x)
    have e5 : x ⬝ᵥ ((Q m - B) *ᵥ x) ≤ nrm1 (Q m - B) := by
      have := e4.2; rw [hx, mul_one] at this; exact this
    linarith
  rw [gap]; linarith

end Brockian.UnbalancedPentagon

import Brockian.MinMax
import Brockian.OpNorm
import Brockian.Spectrum
import Brockian.Range

/-!
# Unbalanced pentagon gap extremals — main module

This module is the entry point of the development.  For positive fibre sizes
`m : Fin 5 → ℝ` on the vertices of the 5-cycle we work with

* `deg m i = m (i-1) + m (i+1)`,
* `Q m i j = √(m i * m j / (deg m i * deg m j))` on the edges of `C₅` and `0` elsewhere,
* `perron m i = √(m i * deg m i)`, which satisfies `Q m *ᵥ perron m = perron m`
  (`Q_mulVec_perron`),
* `gap m = 1 - sec (Q m) (perron m)` where `sec A v` is the supremum of the Rayleigh
  quotient `x ⬝ᵥ (A *ᵥ x)` over unit vectors `x` orthogonal to `v`.

The definition of the gap is *not* vacuous: `gap_eq_one_sub_eigenvalues₀_one` proves

`gap m = 1 - (Q m).eigenvalues₀ 1`,

i.e. the Rayleigh definition on the orthogonal complement of the Perron vector really is
`1` minus the second largest eigenvalue of `Q m`, equivalently the smallest positive
eigenvalue of the normalized Laplacian `1 - Q m`.

## Proved results

1. `gap_lower_bound_of_ratio` : `g5 / rho m ^ 2 ≤ gap m` with `g5 = (5 - √5)/4` and
   `rho m = max m / min m` (weighted Poincaré comparison, `Brockian/LowerBound.lean`,
   with the `C₅` Poincaré constant proved by an explicit SOS certificate in
   `Brockian/Poincare.lean`).
2. `Qa_tendsto_Qmin_opNorm` : `‖Q (avec t) - Qmin‖ → 0`, where `avec t = (t², 1, t², t, t)`
   and `Qmin` carries the edges `{2,3}` and `{4,0}` with weight `1`;
   `Qmin_eigenvalues` : the ordered spectrum of `Qmin` is `1, 1, 0, -1, -1`.
3. `gap_tendsto_zero` : `gap (avec t) → 0`.
4. `Qb_tendsto_Qmax_opNorm` : `‖Q (bvec t) - Qmax‖ → 0`, where `bvec t = (1, 1, t, t², t)`
   and `Qmax` carries the edges `{2,3}` and `{3,4}` with weight `1/√2`;
   `Qmax_eigenvalues` : the ordered spectrum of `Qmax` is `1, 0, 0, 0, -1`.
5. `gap_tendsto_one` : `gap (bvec t) → 1`.
6. `gap_lt_one` : `gap m < 1` for every strictly positive `m`.
7. `gap_sharp_range` : `sInf gapSet = 0`, `sSup gapSet = 1`, and neither endpoint is
   attained, where `gapSet` collects the gaps of positive *integral* fibre sizes.

The eigenvalue continuity used in 3 and 5 is elementary and proved in the project:
`gap_le_nrm1_of_eigen` and `le_gap_of_approx` in `Brockian/Perturb.lean`, together with
`opNorm_le_nrm1` in `Brockian/OpNorm.lean`, which shows that the entrywise `ℓ¹` norm used
there dominates the `ℓ²` operator norm.

## Conjectural improvements (not proved here)

The following statements are *not* part of the formal development; they are recorded only as
informal remarks and no Lean declaration below depends on them.

* The exponent `2` in `g5 / rho m ^ 2 ≤ gap m` is presumably not optimal; numerically a bound
  of the shape `c / rho m` appears to hold for the 5-cycle.
* The convergence rates for the two extremal families appear to be `gap (avec t) = Θ(1/√t)`
  and `1 - gap (bvec t) = Θ(1/√t)`.
-/

namespace Brockian.UnbalancedPentagon

open Matrix Finset Filter Topology
open scoped Matrix.Norms.L2Operator

/-- **The whole package in one statement.**  Each conjunct is one of the required targets;
see the module docstring for the correspondence. -/
