/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is repeated as a module docstring immediately after the import.)

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open scoped ComplexConjugate InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value of a symmetric operator in a state is real. -/

lemma inner_self_apply_conj (X : H →ₗ[ℂ] H) (psi : H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ) :
    conj ⟪psi, X psi⟫_ℂ = ⟪psi, X psi⟫_ℂ := by
  rw [inner_conj_symm, hX]

/-- Robertson-type identity: for symmetric `X`, `P` whose commutator acts on the unit
vector `psi` as multiplication by `i * ℏ`, the mean-shifted vectors
`u = (X - ⟨X⟩)psi`, `v = (P - ⟨P⟩)psi` satisfy `⟪u,v⟫ - ⟪v,u⟫ = i * ℏ`. -/
