import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

noncomputable def bellSchmidt : SchmidtDecomp bellState where
  rank := 2
  lam := fun _ => (Real.sqrt 2)⁻¹
  e := fun k i => if i = k then 1 else 0
  f := fun k j => if j = k then 1 else 0
  lam_pos := fun _ => by positivity
  e_orthonormal := by
    intro k l
    simp [Finset.sum_ite_eq, eq_comm]
  f_orthonormal := by
    intro k l
    simp [Finset.sum_ite_eq, eq_comm]
  eq_sum := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [bellState]

/-- The Schmidt coefficients of the Bell state are `1/√2, 1/√2`. -/
