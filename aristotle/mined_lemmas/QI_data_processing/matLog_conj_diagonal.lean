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

theorem matLog_conj_diagonal (U : unitary (Matrix n n ℂ)) (d : n → ℝ) :
    matLog ((U : Matrix n n ℂ) * diagonal (fun i => (d i : ℂ)) * star (U : Matrix n n ℂ))
      = (U : Matrix n n ℂ) * diagonal (fun i => ((Real.log (d i) : ℝ) : ℂ))
          * star (U : Matrix n n ℂ) := by
  rw [matLog, cfc_unitary_conj U Real.log _ (isSelfAdjoint_diagonal d), cfc_diagonal]

/-! ### Relative entropy of a simultaneously diagonalized pair -/

