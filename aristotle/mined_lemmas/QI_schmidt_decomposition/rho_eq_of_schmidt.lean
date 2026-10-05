/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- comment and is repeated as the module docstring below.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
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

set_option grind.warning false

namespace QI

open scoped ComplexConjugate

variable {m n : ℕ}

/-- The amplitude matrix of a bipartite pure state, i.e. its coordinates in the product basis. -/

lemma rho_eq_of_schmidt {r : ℕ} {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (hd : IsSchmidt ψ lam e f) (p p' : Fin m) :
    rho ψ p p' = ∑ i, ((lam i : ℂ) ^ 2) * e i p * conj (e i p') := by
  obtain ⟨-, -, hfo, hpsi⟩ := hd
  rw [orthonormal_iff_coord] at hfo
  rw [rho_apply]
  have hf' : ∀ i j, ∑ q, f i q * conj (f j q) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    have h := congrArg (starRingEnd ℂ) (hfo i j)
    rw [map_sum] at h
    simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply] at h
    rw [h]
    split_ifs <;> simp
  have expand : ∀ q, ψ (p, q) * conj (ψ (p', q))
      = ∑ i, ∑ j, (((lam i : ℂ) * lam j) * (e i p * conj (e j p'))) * (f i q * conj (f j q)) := by
    intro q
    rw [hpsi (p, q), hpsi (p', q), map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have key : ∀ j, ∑ q, (((lam i : ℂ) * lam j) * (e i p * conj (e j p'))) * (f i q * conj (f j q))
      = (((lam i : ℂ) * lam j) * (e i p * conj (e j p'))) * (if i = j then (1 : ℂ) else 0) := by
    intro j; rw [← hf' i j, Finset.mul_sum]
  simp_rw [key]
  simp [Finset.sum_ite_eq]
  ring

