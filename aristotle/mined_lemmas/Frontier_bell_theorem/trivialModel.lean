/-
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

/-- A local hidden-variable (LHV) model for a bipartite experiment with two measurement
settings per side.  A hidden variable `l : Λ` is drawn from a probability distribution `μ`;
Alice's outcome for setting `i` is `A i l` and Bob's outcome for setting `j` is `B j l`.
Locality is expressed by the fact that `A i l` does not depend on Bob's setting `j`
and `B j l` does not depend on Alice's setting `i`.  Outcomes take values in `[-1, 1]`
(this includes the usual `±1`-valued outcomes). -/
structure LHVModel where
  /-- The space of hidden variables. -/
  Λ : Type*
  /-- Measurable structure on the hidden variables. -/
  measΛ : MeasurableSpace Λ
  /-- The distribution of the hidden variable. -/
  μ : Measure Λ
  /-- `μ` is a probability measure. -/
  isProb : IsProbabilityMeasure μ
  /-- Alice's outcome function, depending only on her setting and the hidden variable. -/
  A : Fin 2 → Λ → ℝ
  /-- Bob's outcome function, depending only on his setting and the hidden variable. -/
  B : Fin 2 → Λ → ℝ
  /-- Measurability of Alice's outcomes. -/
  A_meas : ∀ i, AEStronglyMeasurable (A i) μ
  /-- Measurability of Bob's outcomes. -/
  B_meas : ∀ j, AEStronglyMeasurable (B j) μ
  /-- Alice's outcomes lie in `[-1,1]`. -/
  A_bdd : ∀ i l, |A i l| ≤ 1
  /-- Bob's outcomes lie in `[-1,1]`. -/
  B_bdd : ∀ j l, |B j l| ≤ 1

attribute [instance] LHVModel.measΛ LHVModel.isProb

/-- The correlation predicted by a local hidden-variable model for settings `(i, j)`. -/

noncomputable def trivialModel : LHVModel.{0} where
  Λ := Unit
  measΛ := inferInstance
  μ := Measure.dirac ()
  isProb := by infer_instance
  A := fun _ _ => 1
  B := fun _ _ => 1
  A_meas := fun _ => aestronglyMeasurable_const
  B_meas := fun _ => aestronglyMeasurable_const
  A_bdd := fun _ _ => by norm_num
  B_bdd := fun _ _ => by norm_num

/-- The classical bound is attained: there is a local hidden-variable model whose CHSH value
is exactly `2`.  (In particular the notion of an LHV model is not vacuous.) -/
