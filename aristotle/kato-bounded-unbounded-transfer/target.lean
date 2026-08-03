import Brockian.WeylKatoUnbounded

/-
Harmonic / Aristotle hard target.

This is the classical bounded-perturbation theorem for an unbounded ESA core.
Keep the exact operator `perturb T B` and derive the conclusion from the four
standard hypotheses below. Do not assume `BoundedPerturbationTransfer`, shifted
range density, resolvents, small norm, or the conclusion in another form.
-/
namespace Brockian.HardTargets.KatoBoundedTransfer

open Brockian.Weyl.Operator
open Brockian.Weyl.KatoUnbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem essentiallySelfAdjoint_bounded_perturbation_target
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hT : IsSymmetric T) (hd : Dense (T.domain : Set H))
    (hESA : EssentiallySelfAdjoint T) (hB : IsSelfAdjoint B) :
    EssentiallySelfAdjoint (perturb T B) := by
  sorry

end Brockian.HardTargets.KatoBoundedTransfer
