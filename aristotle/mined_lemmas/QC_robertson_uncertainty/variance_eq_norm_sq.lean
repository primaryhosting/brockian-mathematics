import Mathlib
/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a module,
so the mandated header comment is placed immediately after the single `import Mathlib` line.
-/

namespace QC

open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The expectation value `⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/

lemma variance_eq_norm_sq {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (ψ : E) :
    variance A ψ = ‖centered A ψ ψ‖ ^ 2 := by
  have h := (centered_isSymmetric hA ψ) ψ (centered A ψ ψ)
  rw [variance, ← h]
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (centered A ψ ψ)

/-- `ΔA = ‖(A - ⟨A⟩) ψ‖`. -/
