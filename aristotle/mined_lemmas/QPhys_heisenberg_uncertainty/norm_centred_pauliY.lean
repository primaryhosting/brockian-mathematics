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

lemma norm_centred_pauliY (c : ℝ) (hc : 0 ≤ c) :
    ‖pauliY c basisState - (inner ℂ basisState (pauliY c basisState) : ℂ) • basisState‖ = c := by
  rw [inner_basisState_pauliY, EuclideanSpace.norm_eq]
  simp [pauliY, basisState, Matrix.toLpLin_apply, Fin.sum_univ_succ]
  rw [Real.sqrt_sq hc]

/-- The hypotheses of `heisenberg_uncertainty` are satisfiable for every `ℏ ≥ 0`, and the
bound is sharp: there is a normalized state and a pair of symmetric operators obeying the
canonical commutation relation at that state for which `Δx · Δp = ℏ / 2`. -/
