/-
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is given as a plain block comment and repeated verbatim below.)

import Mathlib

/-!
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open MeasureTheory

/-- A local hidden-variable (LHV) model for a bipartite experiment with two binary
measurement settings per side.

`Ω` is the space of hidden variables, `μ` a probability distribution on it, and
`A i` (resp. `B j`) the deterministic response of Alice (resp. Bob) to setting `i`
(resp. `j`), a measurable function of the hidden variable alone (this is locality:
Alice's outcome does not depend on Bob's setting and conversely), taking values in
`[-1, 1]`. -/
structure LHVModel (Ω : Type*) [MeasurableSpace Ω] where
  /-- the distribution of the hidden variable -/
  μ : Measure Ω
  /-- `μ` is a probability measure -/
  isProb : IsProbabilityMeasure μ
  /-- Alice's response function for each of her two settings -/
  A : Bool → Ω → ℝ
  /-- Bob's response function for each of his two settings -/
  B : Bool → Ω → ℝ
  hA_meas : ∀ i, Measurable (A i)
  hB_meas : ∀ j, Measurable (B j)
  hA_bdd : ∀ i ω, |A i ω| ≤ 1
  hB_bdd : ∀ j ω, |B j ω| ≤ 1

namespace LHVModel

variable {Ω : Type*} [MeasurableSpace Ω] (M : LHVModel Ω)

attribute [instance] LHVModel.isProb

/-- The correlation predicted by the model when Alice uses setting `i` and Bob setting `j`. -/

lemma chsh_eq_integral :
    M.chsh = ∫ ω, (M.A false ω * M.B false ω + M.A false ω * M.B true ω
      + M.A true ω * M.B false ω - M.A true ω * M.B true ω) ∂M.μ := by
  have h1 := integral_add (M.integrable_mul false false) (M.integrable_mul false true)
  have h2 := integral_add ((M.integrable_mul false false).add (M.integrable_mul false true))
    (M.integrable_mul true false)
  have h3 := integral_sub (((M.integrable_mul false false).add (M.integrable_mul false true)).add
    (M.integrable_mul true false)) (M.integrable_mul true true)
  simp only [Pi.add_apply] at h1 h2 h3
  rw [chsh, corr, corr, corr, corr, h3, h2, h1]

end LHVModel

/-- Pointwise CHSH bound: for numbers in `[-1,1]`, the CHSH expression is at most `2`
in absolute value. -/
