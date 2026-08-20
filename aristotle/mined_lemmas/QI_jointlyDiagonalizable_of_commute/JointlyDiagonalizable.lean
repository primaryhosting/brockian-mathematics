import Mathlib
import RequestProject.Holevo

/-!
# Simultaneous diagonalization of a commuting family of Hermitian matrices

The main result `QI.jointlyDiagonalizable_of_commute` shows that a family of pairwise commuting
Hermitian matrices is diagonal in a common orthonormal basis, i.e. satisfies
`QI.JointlyDiagonalizable`.
-/

open Matrix LinearMap
open scoped Function

namespace QI

variable {n X : Type*} [Fintype n] [DecidableEq n]


lemma JointlyDiagonalizable.commute {ρ : X → Matrix n n ℂ} (h : JointlyDiagonalizable ρ)
    (x x' : X) : Commute (ρ x) (ρ x') := by
  obtain ⟨U, hU, hv⟩ := h
  obtain ⟨v, hvx⟩ := hv x
  obtain ⟨w, hwx⟩ := hv x'
  have hUU : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff' (A := U)).1 hU
  have hdd : Matrix.diagonal (fun i => (v i : ℂ)) * Matrix.diagonal (fun i => (w i : ℂ))
      = Matrix.diagonal (fun i => (w i : ℂ)) * Matrix.diagonal (fun i => (v i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact Matrix.diagonal_eq_diagonal_iff.2 fun i => by ring
  show ρ x * ρ x' = ρ x' * ρ x
  rw [hvx, hwx]
  calc U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ *
        (U * Matrix.diagonal (fun i => (w i : ℂ)) * Uᴴ)
      = U * (Matrix.diagonal (fun i => (v i : ℂ)) * (Uᴴ * U) *
          Matrix.diagonal (fun i => (w i : ℂ))) * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal (fun i => (w i : ℂ)) * (Uᴴ * U) *
          Matrix.diagonal (fun i => (v i : ℂ))) * Uᴴ := by
        rw [hUU, mul_one, mul_one, hdd]
    _ = U * Matrix.diagonal (fun i => (w i : ℂ)) * Uᴴ *
          (U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ) := by
        simp only [Matrix.mul_assoc]

/-! ### A sanity check: perfectly distinguishable states -/

/-- Measuring the ensemble `{(1/2, |0⟩⟨0|), (1/2, |1⟩⟨1|)}` in the computational basis yields
one nat (`log 2`) of information; in particular the definitions above are not degenerate. -/
example :
    measInfo (n := Fin 2) (X := Fin 2) (Y := Fin 2) (fun _ => 1 / 2)
      (fun x => Matrix.diagonal (fun i => if i = x then (1 : ℂ) else 0))
      (fun y => Matrix.diagonal (fun i => if i = y then (1 : ℂ) else 0)) = Real.log 2 := by
  have hprob : ∀ x y : Fin 2,
      outcomeProb (Matrix.diagonal (fun i => if i = x then (1 : ℂ) else 0))
        (Matrix.diagonal (fun i => if i = y then (1 : ℂ) else 0)) = if x = y then 1 else 0 := by
    intro x y
    rw [outcomeProb, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    by_cases h : x = y <;> simp [h, Fin.sum_univ_two, Fin.ext_iff] <;>
      fin_cases x <;> fin_cases y <;> simp_all
  rw [measInfo]
  simp only [hprob]
  rw [shannonEntropy]
  have h1 : ∀ y : Fin 2, (∑ x : Fin 2, (1 / 2 : ℝ) * (if x = y then 1 else 0)) = 1 / 2 := by
    intro y; fin_cases y <;> simp
  simp only [h1]
  have h2 : ∀ x : Fin 2, shannonEntropy (fun y : Fin 2 => if x = y then (1 : ℝ) else 0) = 0 := by
    intro x
    rw [shannonEntropy]
    fin_cases x <;> simp [Fin.sum_univ_two]
  simp only [h2]
  simp [Real.negMulLog, Real.log_inv]

/-! ### Elementary matrix facts -/

