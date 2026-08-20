import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Statement: Every bipartite pure state has a Schmidt decomposition with unique Schmidt coefficients.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Finset Matrix
open scoped ComplexConjugate InnerProductSpace

namespace QI

variable {m n : ℕ}

/-- `IsSchmidtDecomposition psi σ u v` says that the bipartite pure state `psi`, a vector of the
tensor product `ℂ^m ⊗ ℂ^n` realized as `EuclideanSpace ℂ (Fin m × Fin n)`, is written as
`psi = ∑ k, σ k • (u k ⊗ v k)` where the `σ k` are strictly positive reals (the Schmidt
coefficients) and `u`, `v` are orthonormal families in the two factors. -/
structure IsSchmidtDecomposition {ι : Type} [Fintype ι]
    (psi : EuclideanSpace ℂ (Fin m × Fin n)) (σ : ι → ℝ)
    (u : ι → EuclideanSpace ℂ (Fin m)) (v : ι → EuclideanSpace ℂ (Fin n)) : Prop where
  coeff_pos : ∀ k, 0 < σ k
  left_orthonormal : Orthonormal ℂ u
  right_orthonormal : Orthonormal ℂ v
  sum_eq : ∀ i j, psi (i, j) = ∑ k, (σ k : ℂ) * u k i * v k j

/-- The matrix of coefficients of a bipartite state in the product basis. -/

lemma inner_yvec (w : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (lam : Fin m → ℝ)
    (hw : ∀ k, (reducedLeft psi) *ᵥ (w k).ofLp = lam k • (w k).ofLp) (k l : Fin m) :
    ⟪yvec psi (fun i => w i) k, yvec psi (fun i => w i) l⟫_ℂ =
      (lam k : ℂ) * (if l = k then 1 else 0) := by
  rw [inner_euclidean]
  have e1 : ∀ j : Fin n, conj (yvec psi (fun i => w i) k j) * yvec psi (fun i => w i) l j
      = ∑ b, ∑ a, (conj ((w l) b) * psi (b, j)) * ((w k) a * conj (psi (a, j))) := by
    intro j
    simp only [yvec_apply, map_sum, map_mul, Complex.conj_conj, ← Finset.sum_mul_sum]
    rw [mul_comm]
  simp only [e1]
  rw [Finset.sum_comm]
  have e2 : ∀ b : Fin m, ∑ j, ∑ a, (conj ((w l) b) * psi (b, j)) * ((w k) a * conj (psi (a, j)))
      = conj ((w l) b) * (((reducedLeft psi) *ᵥ (w k).ofLp) b) := by
    intro b
    rw [Finset.sum_comm]
    simp only [Matrix.mulVec, dotProduct, reducedLeft_apply, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [e2, hw k]
  have h : ∑ b, conj ((w l) b) * (((lam k) • (w k).ofLp) b) = (lam k : ℂ) * ⟪w l, w k⟫_ℂ := by
    rw [inner_euclidean, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [Complex.real_smul]
    ring
  rw [h, orthonormal_iff_ite.mp w.orthonormal l k]

/-- Reconstruction of the coefficient matrix from an orthonormal eigenbasis. -/
