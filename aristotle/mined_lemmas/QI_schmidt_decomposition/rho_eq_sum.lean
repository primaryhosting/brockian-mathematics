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

lemma rho_eq_sum {psi : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi r lam e f) :
    rho psi = Matrix.of fun i i' => ∑ k, ((lam k : ℂ) ^ 2) * e k i * conj (e k i') := by
  have hf : ∀ k l, ∑ j, conj (f k j) * f l j = if k = l then 1 else 0 :=
    (orthonormal_iff_sum f).1 h.right_orthonormal
  ext i i'
  simp only [rho, Matrix.of_apply]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => by
    rw [decomp_apply h i j, decomp_apply h i' j])]
  have key : ∀ k l : Fin r, ∑ j, f k j * conj (f l j) = if k = l then (1:ℂ) else 0 :=
    orthonormal_sum' h.right_orthonormal
  calc (∑ j, (∑ k, (lam k : ℂ) * e k i * f k j) * conj (∑ l, (lam l : ℂ) * e l i' * f l j))
      = ∑ j, ∑ k, ∑ l, ((lam k : ℂ) * e k i * ((lam l : ℂ) * conj (e l i')))
          * (f k j * conj (f l j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        simp only [map_mul, Complex.conj_ofReal]
        ring
    _ = ∑ k, ∑ l, ((lam k : ℂ) * e k i * ((lam l : ℂ) * conj (e l i')))
          * (∑ j, f k j * conj (f l j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ k, ((lam k : ℂ) ^ 2) * e k i * conj (e k i') := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => by rw [key k l])]
        simp
        ring

