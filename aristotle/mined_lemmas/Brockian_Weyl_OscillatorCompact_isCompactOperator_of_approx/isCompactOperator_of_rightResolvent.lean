/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem isCompactOperator_of_rightResolvent {z : ℂ} (hz : |z.im| = 1) (hz' : z.re = 0)
    {R : L2R →L[ℂ] L2R} (hR : RightResolvent harmonicOscillatorPMap.closure z R)
    (hsym : IsSymmetric harmonicOscillatorPMap.closure) :
    IsCompactOperator R := by
  refine isCompactOperator_of_approx R fun ε hε => ?_
  obtain ⟨V, hVfin, hV⟩ := exists_finiteDimensional_approx 2 (ε / 2) (by linarith)
  refine ⟨V, hVfin, fun y hy => ?_⟩
  obtain ⟨v, hvV, hv⟩ :=
    exists_approx_of_mem_closure (C := 2) (by linarith : (0:ℝ) < ε / 2) hV
      (resolvent_mem_closure_goodSet hz hz' hR hsym y hy)
  exact ⟨v, hvV, by linarith [hv]⟩

end Brockian.Weyl.OscillatorCompact

/-
  ClosureResolvent.lean — reconstruction of the corpus modules

  * `Brockian/WeylKatoResolventPackage.lean` (the `RightResolvent` predicate and
    the `ResolventAtI` package),
  * `Brockian/WeylWeightedRellich.lean`      (verbatim),
  * `Brockian/WeylClosedShiftedRanges.lean`  (the construction
    `closureResolventAtIOfEssentiallySelfAdjoint` of the two canonical
    unit-shift resolvents of the closure of an essentially self-adjoint
    symmetric operator).
-/
import RequestProject.Base

open scoped InnerProductSpace

namespace Brockian.Weyl.KatoRellichScaffold

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Right resolvent.** `R` is a bounded right inverse of `T - z`: every `x`
is mapped into the domain of `T` and `(T - z) (R x) = x`. -/
