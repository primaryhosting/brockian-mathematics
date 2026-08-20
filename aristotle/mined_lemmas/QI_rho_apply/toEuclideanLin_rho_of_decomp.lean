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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open Finset Matrix ComplexConjugate

variable {m n : ℕ}

/-- The coefficient matrix of a bipartite vector `ψ ∈ ℂ^m ⊗ ℂ^n`, where the tensor product is
modelled as `EuclideanSpace ℂ (Fin m × Fin n)`. -/

lemma toEuclideanLin_rho_of_decomp {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {σ : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) (v : EuclideanSpace ℂ (Fin m)) :
    Matrix.toEuclideanLin (rho ψ) v = ∑ k, (((σ k ^ 2 : ℝ) : ℂ) * inner ℂ (e k) v) • e k := by
  ext i
  have hL : Matrix.toEuclideanLin (rho ψ) v i = ∑ i', rho ψ i i' * v i' := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  rw [hL]
  have hR : (∑ k, (((σ k ^ 2 : ℝ) : ℂ) * inner ℂ (e k) v) • e k) i
      = ∑ k, (((σ k ^ 2 : ℝ) : ℂ) * inner ℂ (e k) v) * e k i := by
    simp
  rw [hR]
  simp only [rho_apply_of_decomp h, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_eq_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  ring

/-- The eigenspace of the reduced density matrix for a nonzero eigenvalue `t` is spanned by the
Schmidt vectors whose squared coefficient equals `t`. -/
