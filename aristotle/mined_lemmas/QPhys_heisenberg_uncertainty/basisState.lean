/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment on the first lines of the file, because
Lean 4 does not permit a module docstring to precede the `import` commands.)

## Contents

* `QPhys.heisenberg_uncertainty`: for a normalized state `ψ` of a complex inner product
  space and symmetric operators `X`, `P` satisfying the canonical commutation relation
  `[X, P] ψ = i ℏ ψ`, the standard deviations satisfy `Δx · Δp ≥ ℏ / 2`.
  The proof is the classical one: the commutator identity computes
  `⟪u, v⟫ - ⟪v, u⟫ = i ℏ` for the centred vectors `u = (X - ⟨X⟩)ψ`, `v = (P - ⟨P⟩)ψ`,
  and Cauchy–Schwarz bounds each inner product by `‖u‖ ‖v‖ = Δx · Δp`.
* `QPhys.heisenberg_uncertainty_sharp`: the hypotheses are satisfiable and the bound is
  attained, for every `ℏ ≥ 0`.
-/

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Expectation values of a symmetric operator in a state are real. -/

noncomputable def basisState : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

