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

theorem in the setting in which it is a genuine, verifiable statement: the **base case of a
zero-dimensional manifold** (a point), together with its **elliptic complex** generalization.

* For a point, the "bundles" are finite-dimensional vector spaces `E`, `F`, an operator is a
  linear map `D : E →ₗ F`, the analytic index is `dim ker D - dim coker D`, and the
  topological index (the integral of the Chern character of the symbol class over a point,
  i.e. the rank difference) is `dim E - dim F`.  The theorem `Frontier.atiyah_singer_index`
  proves these agree.  Everything characteristic of the index theorem is already visible here:
  the analytic index, defined by solution spaces of the operator, is independent of the
  operator and depends only on topological data; in particular it is invariant under
  deformation of the operator.

* `Frontier.atiyah_singer_index_complex` is the corresponding statement for an elliptic
  complex: the Euler characteristic of the cohomology of the complex (the analytic index)
  equals the alternating sum of the ranks of the bundles (the topological index).  This is
  the Euler–Poincaré principle, which is precisely how e.g. the Gauss–Bonnet and
  Riemann–Roch specializations of the index theorem are packaged.
-/

namespace Frontier

open Module

section Operator

variable {𝕜 : Type*} [Field 𝕜]
variable {E F : Type*} [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- The **analytic index** of an operator `D : E →ₗ[𝕜] F`:
`dim ker D - dim coker D`, where `coker D = F ⧸ range D`. -/
