import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A symmetric (formally self-adjoint) linear operator has real expectation values. -/

lemma abs_im_inner_le (u v : E) : |(⟪u, v⟫_ℂ).im| ≤ ‖u‖ * ‖v‖ :=
  le_trans (Complex.abs_im_le_norm _) (norm_inner_le_norm (𝕜 := ℂ) u v)

/-- **Heisenberg uncertainty principle.**

Let `ψ` be a normalized state in a complex inner product space, and let `X`, `P` be
symmetric (formally self-adjoint) operators satisfying the canonical commutation relation
`[X, P] ψ = i ℏ ψ`.  Then the product of the standard deviations
`Δx = ‖(X - ⟪X⟫)ψ‖` and `Δp = ‖(P - ⟪P⟫)ψ‖` is at least `|ℏ| / 2`.

The proof is the classical one: the commutator gives `Im ⟪(X-⟪X⟫)ψ, (P-⟪P⟫)ψ⟫ = ℏ/2`,
and Cauchy–Schwarz (`norm_inner_le_norm`) bounds this by `Δx · Δp`. -/
