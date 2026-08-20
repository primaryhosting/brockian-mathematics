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

theorem suslinProblemOriginal_iff :
    SuslinProblemOriginal ↔
      ∀ (X : Type) (_ : ConditionallyCompleteLinearOrder X) (_ : TopologicalSpace X),
        Nonempty X → ¬ IsSuslinLine X := by
  constructor
  · intro h X _ _ hX hS
    haveI := hS.orderTopology
    obtain ⟨e⟩ := h X ‹_› ‹_› hS.orderTopology hS.denselyOrdered hS.noMin hS.noMax hX hS.ccc
    exact (isEmpty_homeomorph_real_of_isSuslinLine hS).false e.toHomeomorph
  · intro h X _ _ hot hd hmin hmax hX hccc
    haveI := hot; haveI := hd; haveI := hmin; haveI := hmax; haveI := hX
    have hsep : SeparableSpace X := by
      by_contra hns
      exact h X ‹_› ‹_› hX ⟨hot, hd, hmin, hmax, hccc, hns⟩
    haveI := hsep
    exact orderIso_real_of_separableSpace X

/-- Suslin's Hypothesis implies a positive answer to Suslin's original problem. -/
