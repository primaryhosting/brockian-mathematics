import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace QI

open Matrix Polynomial Finset
open scoped ComplexConjugate ComplexOrder

variable {m n : ℕ}

/-- The elementary tensor `a ⊗ b` of `a ∈ ℂ^m` and `b ∈ ℂ^n`, viewed inside
`ℂ^m ⊗ ℂ^n ≅ ℂ^(m × n)`. -/

lemma orthonormal_sum' {p r : ℕ} {e : Fin r → EuclideanSpace ℂ (Fin p)} (he : Orthonormal ℂ e)
    (k l : Fin r) : ∑ i, e k i * conj (e l i) = if k = l then 1 else 0 := by
  rw [orthonormal_iff_sum] at he
  have h2 : ∑ i, e k i * conj (e l i) = conj (∑ i, conj (e k i) * e l i) := by
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  rw [h2, he k l]
  by_cases hkl : k = l <;> simp [hkl]

/-- An orthonormal basis of `EuclideanSpace ℂ (Fin m)` extending a given orthonormal family. -/
