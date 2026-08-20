import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma spectrum_diagonal19 (d : Fin 19 → ℂ) :
    spectrum ℂ (Matrix.diagonal d) = Set.range d := by
  ext mu
  have hmat : algebraMap ℂ (Matrix (Fin 19) (Fin 19) ℂ) mu - Matrix.diagonal d
      = Matrix.diagonal (fun i => mu - d i) := by
    rw [Matrix.algebraMap_eq_diagonal, ← Matrix.diagonal_sub]
    rfl
  simp only [Set.mem_range, spectrum.mem_iff, hmat, Matrix.isUnit_iff_isUnit_det,
    Matrix.det_diagonal, isUnit_iff_ne_zero, not_not, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero, ne_eq]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, hi.symm⟩
  · rintro ⟨i, hi⟩; exact ⟨i, hi.symm⟩

