import Mathlib
import RequestProject.Classical

/-!
# Quantum relative entropy

Definitions of the matrix logarithm (via the continuous functional calculus), the Umegaki
relative entropy of two density matrices, and quantum channels in Kraus form.
-/

open Matrix Unitary
open scoped BigOperators ComplexOrder

namespace QI

variable {m n ι : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype ι]

/-- The matrix logarithm of a Hermitian matrix, defined through the continuous functional
calculus (with the convention `log 0 = 0`, so that vanishing eigenvalues contribute nothing). -/

theorem cfc_unitary_conj (U : unitary (Matrix n n ℂ)) (f : ℝ → ℝ) (A : Matrix n n ℂ)
    (hA : IsSelfAdjoint A) :
    cfc f ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ))
      = (U : Matrix n n ℂ) * cfc f A * star (U : Matrix n n ℂ) := by
  have hfun : ((conjStarAlgAut ℝ (Matrix n n ℂ) U) : Matrix n n ℂ → Matrix n n ℂ)
      = fun x => (U : Matrix n n ℂ) * x * star (U : Matrix n n ℂ) := rfl
  have hcont : Continuous ((conjStarAlgAut ℝ (Matrix n n ℂ) U) : Matrix n n ℂ → Matrix n n ℂ) := by
    rw [hfun]
    exact (continuous_const.mul continuous_id).mul continuous_const
  have := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) (conjStarAlgAut ℝ (Matrix n n ℂ) U) f A
    (by rw [continuousOn_iff_continuous_restrict]; fun_prop) hcont hA
  simpa using this.symm

/-- `matLog` of a diagonalized matrix. -/
