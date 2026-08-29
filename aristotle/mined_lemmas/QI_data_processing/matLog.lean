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

noncomputable def matLog (A : Matrix n n ℂ) : Matrix n n ℂ := cfc Real.log A

/-- The Umegaki relative entropy `D(ρ‖σ) = Tr ρ (log ρ - log σ)` of two density matrices. -/
