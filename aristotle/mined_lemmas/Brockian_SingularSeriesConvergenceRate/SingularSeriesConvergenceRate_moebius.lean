import Mathlib

/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter

namespace Brockian

/-- The truncated singular series: the partial sum `∑_{q = 1}^{Q} a q` of the local
densities `a q`. -/

theorem SingularSeriesConvergenceRate_moebius :
    ∃ S : ℝ,
      Tendsto
        (fun Q => singularPartial
          (fun q => (ArithmeticFunction.moebius q : ℝ) / (q : ℝ) ^ 2) Q) atTop (nhds S) ∧
      ∀ Q : ℕ, 1 ≤ Q →
        |S - singularPartial
          (fun q => (ArithmeticFunction.moebius q : ℝ) / (q : ℝ) ^ 2) Q| ≤ 1 / (Q : ℝ) := by
  refine SingularSeriesConvergenceRate (C := 1) ?_
  intro q _
  have hmu : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    have : |ArithmeticFunction.moebius q| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
    exact_mod_cast this
  rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (q : ℝ) ^ 2)]
  gcongr

end Brockian

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

