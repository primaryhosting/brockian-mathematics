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
