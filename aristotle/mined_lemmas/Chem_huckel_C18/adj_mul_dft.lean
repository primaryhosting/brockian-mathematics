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

open Matrix

/-- The standard additive character `x ↦ exp (2 π i x / 18)` on `ZMod 18`. -/

lemma adj_mul_dft : cycAdj * dftMat = dftMat * Matrix.diagonal eigval := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have key : ∀ m : ZMod 18, cycAdj j m * dftMat m k
      = (if m = j - 1 then psi (m * k) else 0) + (if m = j + 1 then psi (m * k) else 0) := by
    intro m
    rw [cycAdj_apply, dftMat, Matrix.of_apply]
    by_cases h1 : m = j - 1
    · have h2 : m ≠ j + 1 := by rw [h1]; exact sub_one_ne_add_one j
      rw [if_pos (Or.inl h1), if_pos h1, if_neg h2]; ring
    · by_cases h2 : m = j + 1
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]; ring
      · rw [if_neg (by tauto), if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl (fun m _ => key m), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (j - 1) (fun m => psi (m * k)),
    Finset.sum_ite_eq' Finset.univ (j + 1) (fun m => psi (m * k))]
  simp only [Finset.mem_univ, if_true]
  rw [dftMat, eigval, Matrix.of_apply]
  rw [show (j - 1) * k = j * k + -k by ring, show (j + 1) * k = j * k + k by ring,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring

