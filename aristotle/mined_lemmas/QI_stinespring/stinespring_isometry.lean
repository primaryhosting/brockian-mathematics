import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder MatrixOrder

namespace QI

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The partial trace over the second (environment) tensor factor. -/

theorem stinespring_isometry (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hcp : IsCompletelyPositive Φ) (htp : IsTracePreserving Φ) :
    ∃ (k : ℕ) (V : Matrix (B × Fin (k + 1)) A ℂ),
      Vᴴ * V = 1 ∧ ∀ ρ : Matrix A A ℂ, Φ ρ = ptraceRight (V * ρ * Vᴴ) := by
  classical
  obtain ⟨K, hK⟩ := exists_kraus Φ hcp
  have hsum := kraus_sum_conjTranspose_mul_self K Φ htp hK
  obtain ⟨k, G, hG⟩ := exists_fin_reindex K
  have h1 : ∑ i : Fin (k + 1), (G i)ᴴ * G i = 1 := by
    rw [hG (fun X => Xᴴ * X) (by simp), hsum]
  have h2 : ∀ ρ : Matrix A A ℂ, ∑ i : Fin (k + 1), G i * ρ * (G i)ᴴ = Φ ρ := by
    intro ρ
    rw [hG (fun X => X * ρ * Xᴴ) (by simp), ← hK ρ]
  refine ⟨k, Matrix.of fun p a => G p.2 p.1 a, ?_, ?_⟩
  · ext a a'
    rw [← h1]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.sum_apply,
      Fintype.sum_prod_type]
    exact Finset.sum_comm
  · intro ρ
    ext b b'
    rw [← h2 ρ]
    simp only [ptraceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.sum_apply]

/-- **Stinespring dilation, unitary form.**  Every CPTP map `Φ` on the matrix algebra of a
finite dimensional system `A` is the restriction of a unitary evolution on a larger system:
there are an environment `Fin k` with a pure reference state `e`, and a unitary `U` on
`A ⊗ Fin k`, such that `Φ ρ = Tr_E (U (ρ ⊗ |e⟩⟨e|) Uᴴ)` for all `ρ`. -/
