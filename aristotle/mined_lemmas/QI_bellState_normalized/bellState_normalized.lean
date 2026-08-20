import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma bellState_normalized : ∑ x, ‖bellState x‖ ^ 2 = 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, bellState, Complex.norm_real]
  field_simp
  linarith [h2]

/-- An explicit Schmidt decomposition of the Bell state. -/
