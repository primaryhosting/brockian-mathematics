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

lemma roots_charpoly_rho {psi : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi r lam e f) :
    (rho psi).charpoly.roots =
      Multiset.replicate (m - r) 0 + Finset.univ.val.map (fun k => ((lam k : ℂ) ^ 2)) := by
  rw [charpoly_rho h]
  set a : Fin r → ℂ := fun k => ((lam k : ℂ) ^ 2) with ha
  have hprod : (∏ k : Fin r, ((X : ℂ[X]) - C (a k)))
      = (Multiset.map (fun x => X - C x) (Finset.univ.val.map a)).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  have h1 : ((X : ℂ[X]) ^ (m - r)) ≠ 0 := pow_ne_zero _ X_ne_zero
  have h2 : (∏ k : Fin r, ((X : ℂ[X]) - C (a k))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => X_sub_C_ne_zero _
  rw [Polynomial.roots_mul (mul_ne_zero h1 h2), Polynomial.roots_pow, Polynomial.roots_X, hprod,
    Polynomial.roots_multiset_prod_X_sub_C]
  congr 1
  simp [Multiset.nsmul_singleton]

/-- Existence of a Schmidt decomposition. -/
