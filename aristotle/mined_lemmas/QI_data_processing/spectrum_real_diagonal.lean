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

theorem spectrum_real_diagonal (d : n → ℝ) :
    spectrum ℝ (diagonal fun i => (d i : ℂ)) ⊆ Set.range d := by
  intro r hr
  by_contra hrange
  rw [spectrum.mem_iff] at hr
  apply hr
  have hdiag : algebraMap ℝ (Matrix n n ℂ) r - (diagonal fun i => (d i : ℂ))
      = diagonal (fun i => ((r : ℂ) - (d i : ℂ))) := by
    rw [Matrix.algebraMap_eq_diagonal, ← Matrix.diagonal_sub]
    rfl
  rw [hdiag, Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  rw [isUnit_iff_ne_zero]
  simp only [sub_ne_zero]
  intro h
  exact hrange ⟨i, by exact_mod_cast h.symm⟩

