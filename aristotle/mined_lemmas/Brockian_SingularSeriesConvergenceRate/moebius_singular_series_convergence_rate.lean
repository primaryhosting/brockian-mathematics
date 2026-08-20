/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- Telescoping tail estimate: for `Q ≥ 1`,
`∑_{i < n} 1/(i+Q+1)^2 ≤ 1/Q - 1/(Q+n)`. -/

theorem moebius_singular_series_convergence_rate (w : ℕ → ℝ) (hw : ∀ q : ℕ, |w q| ≤ 1) :
    Summable (fun q : ℕ => ((ArithmeticFunction.moebius q : ℤ) : ℝ) * w q / (q : ℝ) ^ 2) ∧
      ∀ Q : ℕ, 1 ≤ Q →
        |(∑' q : ℕ, ((ArithmeticFunction.moebius q : ℤ) : ℝ) * w q / (q : ℝ) ^ 2)
            - ∑ q ∈ Finset.Icc 1 Q,
                ((ArithmeticFunction.moebius q : ℤ) : ℝ) * w q / (q : ℝ) ^ 2| ≤ 1 / (Q : ℝ) := by
  refine SingularSeriesConvergenceRate _ 1 (by simp) (fun q hq => ?_)
  have hmu : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
    rcases eq_or_ne (ArithmeticFunction.moebius q) 0 with h | h
    · simp [h]
    · rcases (ArithmeticFunction.moebius_ne_zero_iff_eq_or).1 h with h1 | h1 <;> simp [h1]
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (q : ℝ) ^ 2), abs_mul]
  gcongr
  exact mul_le_one₀ hmu (abs_nonneg _) (hw q)

/-- Sanity check / instance of the general bound: the hypotheses are satisfiable, e.g. for
`a q = 1/q²` (with the convention `a 0 = 0`), where truncation at `Q` costs at most `1/Q`. -/
example : ∀ Q : ℕ, 1 ≤ Q →
    |(∑' q : ℕ, (1 : ℝ) / (q : ℝ) ^ 2) - ∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q : ℝ) ^ 2|
      ≤ 1 / (Q : ℝ) :=
  (SingularSeriesConvergenceRate (fun q => 1 / (q : ℝ) ^ 2) 1 (by norm_num)
    (fun q hq => by
      have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      rw [abs_of_nonneg (by positivity)])).2

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

