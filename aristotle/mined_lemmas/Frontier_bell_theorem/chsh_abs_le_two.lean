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
