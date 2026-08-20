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

lemma c5_sos (s a b c d e : ℝ) (hs : s ^ 2 = 5) (hs0 : 0 < s) :
    0 ≤ ((a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - e) ^ 2 + (e - a) ^ 2)
      - ((5 - s) / 2) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2)
      + ((5 - s) / 10) * (a + b + c + d + e) ^ 2 := by
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F =
      ((a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - e) ^ 2 + (e - a) ^ 2)
      - ((5 - s) / 2) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2)
      + ((5 - s) / 10) * (a + b + c + d + e) ^ 2 := ⟨_, rfl⟩
  rw [← hF]
  have key : (4 * s * a - (5 + s) * (e + b) + (5 - s) * (d + c)) ^ 2
      + (4 * s * b - (5 + s) * (a + c) + (5 - s) * (e + d)) ^ 2
      + (4 * s * c - (5 + s) * (b + d) + (5 - s) * (a + e)) ^ 2
      + (4 * s * d - (5 + s) * (c + e) + (5 - s) * (b + a)) ^ 2
      + (4 * s * e - (5 + s) * (d + a) + (5 - s) * (c + b)) ^ 2 = 100 * s * F := by
    rw [hF]
    linear_combination (5 * (a + b + c + d + e) ^ 2
      - 25 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2)) * hs
  have h1 : (0:ℝ) ≤ 100 * s * F := by rw [← key]; positivity
  nlinarith [h1, hs0]

/-- **Poincaré inequality for `C₅`** in homogeneous form:
`2 g₅ ∑ y i ^ 2 ≤ ∑ (y i - y (i+1))^2 + (2 g₅ / 5) (∑ y i)^2`. -/
