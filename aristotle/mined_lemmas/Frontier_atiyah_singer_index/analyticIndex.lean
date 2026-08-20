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

noncomputable def analyticIndex (D : E →ₗ[𝕜] F) : ℤ :=
  (finrank 𝕜 (LinearMap.ker D) : ℤ) - (finrank 𝕜 (F ⧸ LinearMap.range D) : ℤ)

/-- The **topological index** of the symbol data `(E, F)` over a point: the difference of the
ranks of the two bundles, i.e. `∫_pt ch(E - F)`. -/
