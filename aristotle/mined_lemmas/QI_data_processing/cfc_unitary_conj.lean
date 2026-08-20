import RequestProject.Kron

/-!
# Vectorization, the modular operator and relative entropy

We vectorize matrices, express the relative entropy `Tr ρ log ρ - Tr ρ log σ` as (minus) a
quadratic form of `log (σ ⊗ (ρ⁻¹)ᵀ)` at the vectorization of `√ρ`, and record the
variational ("completing the square") characterization of resolvent quadratic forms.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m N : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype N] [DecidableEq N]

/-! ### Vectorization -/

/-- Vectorization of a matrix: the vector of all its entries, indexed by pairs. -/

theorem cfc_unitary_conj {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ))
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f (U * A * Uᴴ) = U * (cfc f A) * Uᴴ := by
  set φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) ⟨U, hU⟩ with hφ
  have happ : ∀ X, φ X = U * X * Uᴴ := by
    intro X; rw [hφ, Unitary.conjStarAlgAut_apply]; rfl
  have hcont : Continuous (φ : Matrix n n ℂ → Matrix n n ℂ) := by
    have h2 : (fun X => φ X) = fun X => U * X * Uᴴ := by funext X; exact happ X
    rw [show (φ : Matrix n n ℂ → Matrix n n ℂ) = fun X => φ X from rfl, h2]; fun_prop
  have hst : IsSelfAdjoint (φ A) := by
    rw [IsSelfAdjoint, ← map_star]; congr 1
  have h := StarAlgHomClass.map_cfc (S := ℂ) φ f A
    (Set.Finite.continuousOn (Set.toFinite _) f) hcont hA hst
  rw [← happ, ← happ, ← h]

/-- **Functional calculus through an arbitrary unitary diagonalization.** -/
