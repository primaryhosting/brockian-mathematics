import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

def IsONFamily {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (v : ι → (Fin d → ℂ)) : Prop :=
  ∀ k l, ∑ i, (starRingEnd ℂ) (v k i) * v l i = if k = l then 1 else 0

/-- A Schmidt decomposition of the bipartite pure state `psi`. -/
structure SchmidtDecomp (psi : Fin m × Fin n → ℂ) where
  /-- The Schmidt rank. -/
  rank : ℕ
  /-- The Schmidt coefficients. -/
  lam : Fin rank → ℝ
  /-- The orthonormal family on the first factor. -/
  e : Fin rank → (Fin m → ℂ)
  /-- The orthonormal family on the second factor. -/
  f : Fin rank → (Fin n → ℂ)
  lam_pos : ∀ k, 0 < lam k
  e_orthonormal : IsONFamily e
  f_orthonormal : IsONFamily f
  eq_sum : ∀ i j, psi (i, j) = ∑ k, (lam k : ℂ) * e k i * f k j

/-- The multiset of Schmidt coefficients of a Schmidt decomposition. -/
