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

lemma wcoef_inner (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (j k : Fin m) :
    ∑ q, conj (wcoef ψ j q) * wcoef ψ k q = if j = k then (evals ψ j : ℂ) else 0 := by
  simp only [wcoef]
  have step1 : ∀ q, conj (∑ p, conj (evecs ψ j p) * ψ (p, q))
        * (∑ p, conj (evecs ψ k p) * ψ (p, q))
      = ∑ p, ∑ p', (evecs ψ j p * conj (evecs ψ k p')) * (ψ (p', q) * conj (ψ (p, q))) := by
    intro q
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
    simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    ring
  simp_rw [step1]
  rw [Finset.sum_comm]
  have swap2 : ∀ p, ∑ q, ∑ p', (evecs ψ j p * conj (evecs ψ k p')) * (ψ (p', q) * conj (ψ (p, q)))
      = ∑ p', (evecs ψ j p * conj (evecs ψ k p')) * rho ψ p' p := by
    intro p
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [rho_apply, Finset.mul_sum]
  simp_rw [swap2]
  rw [Finset.sum_comm]
  have inner1 : ∀ p', ∑ p, (evecs ψ j p * conj (evecs ψ k p')) * rho ψ p' p
      = conj (evecs ψ k p') * ((evals ψ j : ℂ) * evecs ψ j p') := by
    intro p'
    rw [← rho_mulVec_evecs ψ j p', Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  simp_rw [inner1]
  have hlast : ∑ p', conj (evecs ψ k p') * ((evals ψ j : ℂ) * evecs ψ j p')
      = (evals ψ j : ℂ) * ∑ p', conj (evecs ψ k p') * evecs ψ j p' := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p' _ => by ring
  rw [hlast, evecs_ortho ψ k j]
  by_cases h : j = k
  · simp [h]
  · simp [h, Ne.symm h]

