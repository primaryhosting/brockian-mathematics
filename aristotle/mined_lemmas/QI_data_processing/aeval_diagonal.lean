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

theorem aeval_diagonal (d : n → ℝ) (P : Polynomial ℝ) :
    (Polynomial.aeval (diagonal fun i => (d i : ℂ))) P
      = diagonal (fun i => ((P.eval (d i) : ℝ) : ℂ)) := by
  have h1 : (diagonal fun i => (d i : ℂ)) = Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) := rfl
  rw [h1, Polynomial.aeval_algHom_apply]
  have h3 : (Polynomial.aeval (fun i => (d i : ℂ))) P = fun i => ((P.eval (d i) : ℝ) : ℂ) := by
    funext i
    have hpi := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : n => ℂ) i)
      (fun j => (d j : ℂ)) P
    simp only [Pi.evalAlgHom_apply] at hpi
    rw [← hpi]
    have h2 := Polynomial.aeval_algHom_apply (Algebra.ofId ℝ ℂ) (d i) P
    simp only [Algebra.ofId_apply] at h2
    simpa using h2
  rw [h3]
  rfl

/-- The continuous functional calculus of a real diagonal matrix acts entrywise. -/
