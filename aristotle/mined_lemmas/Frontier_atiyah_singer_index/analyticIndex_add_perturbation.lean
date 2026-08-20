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

theorem analyticIndex_add_perturbation [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (D K : E →ₗ[𝕜] F) : analyticIndex (D + K) = analyticIndex D :=
  analyticIndex_eq_analyticIndex _ _

/-- Sanity check (non-vacuity): the zero operator from a rank `3` bundle to a rank `2` bundle
over a point has index `3 - 2 = 1`. -/
example : analyticIndex (0 : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) = 1 := by
  rw [atiyah_singer_index]
  simp [topologicalIndex]

end Operator

section Complex

variable {𝕜 : Type*} [Field 𝕜]

/-- The cohomology `ker g / im f` of a two-step complex `A --f--> B --g--> C`. -/
abbrev cohomologyAt {A B C : Type*} [AddCommGroup A] [Module 𝕜 A] [AddCommGroup B]
    [Module 𝕜 B] [AddCommGroup C] [Module 𝕜 C] (f : A →ₗ[𝕜] B) (g : B →ₗ[𝕜] C) : Type _ :=
  (LinearMap.ker g) ⧸ ((LinearMap.range f).comap (LinearMap.ker g).subtype)

/-- The dimension of the cohomology of `A --f--> B --g--> C` at `B` is
`dim ker g - dim im f`. -/
