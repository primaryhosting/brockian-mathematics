import Mathlib

/-!
# Bell's theorem (CHSH form)

We formalise a *local hidden variable* (LHV) model: a probability space `(Λ, μ)` of hidden
variables together with response functions `A i : Λ → ℝ` for Alice's two settings `i : Bool`
and `B j : Λ → ℝ` for Bob's two settings `j : Bool`, each taking values in `[-1, 1]`.
Locality is built into the shape of the model: `A i x` does not depend on Bob's setting `j`
and `B j x` does not depend on Alice's setting `i`; the only shared resource is `x`.

The correlation predicted by such a model for settings `(i, j)` is `∫ x, A i x * B j x ∂μ`.

* `Frontier.LocalHiddenVariableModel.chsh_abs_le_two` : every LHV model satisfies the CHSH
  inequality `|E(0,0) + E(0,1) + E(1,0) - E(1,1)| ≤ 2`.
* `Frontier.bell_theorem` : no LHV model reproduces the quantum-mechanical singlet
  correlations at the optimal CHSH settings (all equal to `√2/2` except the last, `-√2/2`),
  whose CHSH value is Tsirelson's bound `2√2 > 2`.
-/

namespace Frontier

open MeasureTheory

/-- A local hidden variable model with two measurement settings per party.
The hidden variable ranges over a probability space `(Λ, μ)`; Alice's outcome for setting
`i : Bool` is `A i x` and Bob's outcome for setting `j : Bool` is `B j x`, both in `[-1,1]`. -/
structure LocalHiddenVariableModel (Λ : Type*) [MeasurableSpace Λ] where
  /-- The distribution of the hidden variable. -/
  μ : Measure Λ
  /-- `μ` is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure μ
  /-- Alice's response function for each of her two settings. -/
  A : Bool → Λ → ℝ
  /-- Bob's response function for each of his two settings. -/
  B : Bool → Λ → ℝ
  A_meas : ∀ i, AEStronglyMeasurable (A i) μ
  B_meas : ∀ j, AEStronglyMeasurable (B j) μ
  A_bdd : ∀ i x, |A i x| ≤ 1
  B_bdd : ∀ j x, |B j x| ≤ 1

namespace LocalHiddenVariableModel

variable {Λ : Type*} [MeasurableSpace Λ] (M : LocalHiddenVariableModel Λ)

attribute [instance] LocalHiddenVariableModel.isProbabilityMeasure

/-- The correlation predicted by the model for the pair of settings `(i, j)`. -/
noncomputable def corr (i j : Bool) : ℝ := ∫ x, M.A i x * M.B j x ∂M.μ

lemma integrable_prod (i j : Bool) :
    Integrable (fun x => M.A i x * M.B j x) M.μ := by
  refine (integrable_const (1 : ℝ)).mono' (((M.A_meas i).mul (M.B_meas j))) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_one₀ (M.A_bdd i x) (abs_nonneg _) (M.B_bdd j x)

/-- Pointwise CHSH bound for numbers in `[-1,1]`. -/
lemma chsh_pointwise {a0 a1 b0 b1 : ℝ} (h0 : |a0| ≤ 1) (h1 : |a1| ≤ 1)
    (g0 : |b0| ≤ 1) (g1 : |b1| ≤ 1) :
    |a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1| ≤ 2 := by
  have key : |b0 + b1| + |b0 - b1| ≤ 2 := by
    rw [abs_le] at g0 g1
    rcases abs_cases (b0 + b1) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (b0 - b1) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
        rw [e1, e2] <;> linarith [g0.1, g0.2, g1.1, g1.2]
  have step : a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1 = a0 * (b0 + b1) + a1 * (b0 - b1) := by ring
  rw [step]
  calc |a0 * (b0 + b1) + a1 * (b0 - b1)| ≤ |a0 * (b0 + b1)| + |a1 * (b0 - b1)| := abs_add_le _ _
    _ = |a0| * |b0 + b1| + |a1| * |b0 - b1| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * |b0 + b1| + 1 * |b0 - b1| := by gcongr
    _ ≤ 2 := by linarith

/-- **CHSH inequality**: any local hidden variable model has CHSH value at most `2`. -/
theorem chsh_abs_le_two :
    |M.corr false false + M.corr false true + M.corr true false - M.corr true true| ≤ 2 := by
  have e1 : ∫ x, (M.A false x * M.B false x + M.A false x * M.B true x) ∂M.μ
      = M.corr false false + M.corr false true :=
    integral_add (M.integrable_prod false false) (M.integrable_prod false true)
  have e2 : ∫ x, (M.A false x * M.B false x + M.A false x * M.B true x
        + M.A true x * M.B false x) ∂M.μ
      = (∫ x, (M.A false x * M.B false x + M.A false x * M.B true x) ∂M.μ)
        + M.corr true false :=
    integral_add ((M.integrable_prod false false).add (M.integrable_prod false true))
      (M.integrable_prod true false)
  have e3 : ∫ x, (M.A false x * M.B false x + M.A false x * M.B true x
        + M.A true x * M.B false x - M.A true x * M.B true x) ∂M.μ
      = (∫ x, (M.A false x * M.B false x + M.A false x * M.B true x
          + M.A true x * M.B false x) ∂M.μ) - M.corr true true :=
    integral_sub (((M.integrable_prod false false).add (M.integrable_prod false true)).add
      (M.integrable_prod true false)) (M.integrable_prod true true)
  have hsum : M.corr false false + M.corr false true + M.corr true false - M.corr true true
      = ∫ x, (M.A false x * M.B false x + M.A false x * M.B true x
              + M.A true x * M.B false x - M.A true x * M.B true x) ∂M.μ := by
    rw [e3, e2, e1]
  rw [hsum, ← Real.norm_eq_abs]
  have hbound : ∀ x, ‖M.A false x * M.B false x + M.A false x * M.B true x
      + M.A true x * M.B false x - M.A true x * M.B true x‖ ≤ 2 := by
    intro x
    exact chsh_pointwise (M.A_bdd false x) (M.A_bdd true x) (M.B_bdd false x) (M.B_bdd true x)
  calc ‖∫ x, (M.A false x * M.B false x + M.A false x * M.B true x
              + M.A true x * M.B false x - M.A true x * M.B true x) ∂M.μ‖
      ≤ 2 * (M.μ Set.univ).toReal :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound)
    _ = 2 := by simp

/-- Local hidden variable models do exist (deterministic, uncorrelated outcomes on a
one-point hidden-variable space); so the theorems above are not vacuous. -/
noncomputable def const : LocalHiddenVariableModel PUnit where
  μ := Measure.dirac PUnit.unit
  isProbabilityMeasure := inferInstance
  A := fun _ _ => 1
  B := fun _ _ => 1
  A_meas := fun _ => aestronglyMeasurable_const
  B_meas := fun _ => aestronglyMeasurable_const
  A_bdd := by simp
  B_bdd := by simp

end LocalHiddenVariableModel

/-- **Bell's theorem.** No local hidden variable model reproduces the quantum-mechanical
correlations of a singlet state at the optimal CHSH measurement settings, where the four
correlations are `√2/2, √2/2, √2/2, -√2/2` and the CHSH value equals Tsirelson's bound
`2√2 > 2`. -/
theorem bell_theorem {Λ : Type*} [MeasurableSpace Λ] (M : LocalHiddenVariableModel Λ) :
    ¬ (M.corr false false = Real.sqrt 2 / 2 ∧ M.corr false true = Real.sqrt 2 / 2 ∧
       M.corr true false = Real.sqrt 2 / 2 ∧ M.corr true true = -(Real.sqrt 2 / 2)) := by
  rintro ⟨h1, h2, h3, h4⟩
  have hb := M.chsh_abs_le_two
  rw [h1, h2, h3, h4] at hb
  have hs : (1 : ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 1 < Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this
  rw [abs_le] at hb
  linarith [hb.2]

end Frontier

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

