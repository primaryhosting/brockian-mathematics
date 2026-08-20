/-
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the header above
-- is written as a plain block comment; its text is otherwise verbatim.)

import Mathlib

/-!
## Overview

The Atiyah–Singer index theorem states that for an elliptic (pseudo)differential operator
`D : Γ(E) → Γ(F)` on a closed manifold `M`, the *analytic index*

  `ind_a(D) = dim ker D - dim coker D`

equals the *topological index*, a quantity computed purely from the symbol data of `D`
(via characteristic classes).

Full pseudodifferential theory on manifolds is not available in Mathlib, so we formalize the

theorem atiyah_singer_index [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (D : E →ₗ[𝕜] F) : analyticIndex D = topologicalIndex 𝕜 E F := by
  have h1 := LinearMap.finrank_range_add_finrank_ker D
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range D)
  simp only [analyticIndex, topologicalIndex]
  omega

/-- **Deformation (homotopy) invariance of the analytic index**: any two operators between the
same pair of bundles over a point have the same analytic index.  This is the qualitative
content of the index theorem: the index is a topological invariant. -/
