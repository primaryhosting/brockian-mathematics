import Mathlib
import RequestProject.CantorDedekind

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open TopologicalSpace Set

namespace Frontier

/-- The **countable chain condition** (ccc) for a topological space `X`: every family of
pairwise disjoint nonempty open subsets of `X` is countable. -/

theorem orderIso_real_of_separableSpace (X : Type) [ConditionallyCompleteLinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [DenselyOrdered X] [NoMinOrder X] [NoMaxOrder X]
    [Nonempty X] [TopologicalSpace.SeparableSpace X] : Nonempty (X ≃o ℝ) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  refine orderIso_real_of_countable_orderDense D hDc ?_
  intro a b hab
  obtain ⟨c, hc⟩ := hDd.inter_open_nonempty (Ioo a b) isOpen_Ioo (nonempty_Ioo.mpr hab)
  exact ⟨c, hc.2, hc.1.1, hc.1.2⟩

/-- Sanity check that the hypotheses above are satisfiable: `ℝ` itself is a nonempty,
conditionally complete, densely ordered separable linear order without endpoints. -/
example : Nonempty (ℝ ≃o ℝ) := orderIso_real_of_separableSpace ℝ

end Frontier

