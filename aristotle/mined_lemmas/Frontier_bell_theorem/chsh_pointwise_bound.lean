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

lemma chsh_pointwise_bound {a0 a1 b0 b1 : ℝ} (ha0 : |a0| ≤ 1) (ha1 : |a1| ≤ 1)
    (hb0 : |b0| ≤ 1) (hb1 : |b1| ≤ 1) : |a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1| ≤ 2 := by
  have h1 : a0 * (b0 + b1) ≤ |b0 + b1| :=
    le_trans (le_abs_self _)
      (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ha0)
  have h2 : a1 * (b0 - b1) ≤ |b0 - b1| :=
    le_trans (le_abs_self _)
      (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ha1)
  have h1' : -(a0 * (b0 + b1)) ≤ |b0 + b1| :=
    le_trans (neg_le_abs _)
      (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ha0)
  have h2' : -(a1 * (b0 - b1)) ≤ |b0 - b1| :=
    le_trans (neg_le_abs _)
      (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ha1)
  have key : |b0 + b1| + |b0 - b1| ≤ 2 := by
    rcases abs_cases (b0 + b1) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (b0 - b1) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
        rw [e1, e2] <;> rw [abs_le] at hb0 hb1 <;> linarith [hb0.1, hb0.2, hb1.1, hb1.2]
  rw [abs_le]
  constructor <;> nlinarith

/-- **Bell/CHSH inequality**: every local hidden-variable model satisfies `|CHSH| ≤ 2`. -/
