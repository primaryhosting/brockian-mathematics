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

theorem exists_fin_reindex {ι : Type} [Fintype ι] (K : ι → Matrix B A ℂ) :
    ∃ (k : ℕ) (G : Fin (k + 1) → Matrix B A ℂ),
      ∀ {M : Type} [AddCommMonoid M] (f : Matrix B A ℂ → M), f 0 = 0 →
        ∑ i, f (G i) = ∑ μ, f (K μ) := by
  classical
  refine ⟨Fintype.card ι, fun i => if h : (i : ℕ) < Fintype.card ι then
    K ((Fintype.equivFin ι).symm ⟨i, h⟩) else 0, ?_⟩
  intro M _ f hf
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg,
    not_false_iff, hf, add_zero, Fin.eta]
  exact Fintype.sum_equiv (Fintype.equivFin ι).symm _ _ fun i => rfl

/-- **Stinespring dilation, isometric form.**  Every completely positive trace preserving map
`Φ` on matrix algebras can be written as `Φ ρ = Tr_E (V ρ Vᴴ)` for an isometry
`V : ℂ^A → ℂ^B ⊗ ℂ^E`. -/
