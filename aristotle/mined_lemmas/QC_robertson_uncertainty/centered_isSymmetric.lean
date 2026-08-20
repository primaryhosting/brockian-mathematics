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

lemma centered_isSymmetric {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (ψ : E) :
    (centered A ψ).IsSymmetric := by
  intro x y
  simp only [centered, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    conj_expect_of_isSymmetric hA ψ, hA x y]

/-- The variance is the squared norm of `(A - ⟨A⟩) ψ`. -/
