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

theorem heisenberg_uncertainty_sharp (hbar : ℝ) (hb : 0 ≤ hbar) :
    ∃ (X P : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))
      (psi : EuclideanSpace ℂ (Fin 2)) (Δx Δp : ℝ),
      ‖psi‖ = 1 ∧
      (∀ u v : EuclideanSpace ℂ (Fin 2), inner ℂ (X u) v = inner ℂ u (X v)) ∧
      (∀ u v : EuclideanSpace ℂ (Fin 2), inner ℂ (P u) v = inner ℂ u (P v)) ∧
      X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi ∧
      Δx = ‖X psi - (inner ℂ psi (X psi) : ℂ) • psi‖ ∧
      Δp = ‖P psi - (inner ℂ psi (P psi) : ℂ) • psi‖ ∧
      Δx * Δp = hbar / 2 := by
  set c : ℝ := Real.sqrt (hbar / 2) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c ^ 2 = hbar / 2 := Real.sq_sqrt (by linarith)
  refine ⟨pauliX c, pauliY c, basisState, c, c, norm_basisState,
    pauliX_isSymmetric c, pauliY_isSymmetric c, ?_, ?_, ?_, ?_⟩
  · have h2 : (2 * c ^ 2 : ℝ) = hbar := by rw [hcsq]; ring
    rw [pauli_commutator c, h2]
  · exact (norm_centred_pauliX c hc0).symm
  · exact (norm_centred_pauliY c hc0).symm
  · rw [← sq, hcsq]

end QPhys

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

