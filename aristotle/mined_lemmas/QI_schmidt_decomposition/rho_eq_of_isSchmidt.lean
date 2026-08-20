/-
Header (Lean requires `import` to precede any command, including a module docstring,
so the required header is reproduced verbatim as a module docstring just below the import):

# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

open Matrix

/-- The standard Hermitian inner product on `ℂ^d`, `⟪x, y⟫ = ∑ i, conj (x i) * y i`. -/

theorem rho_eq_of_isSchmidt {m n r : ℕ} {ψ : Fin m → Fin n → ℂ} {σ : Fin r → ℝ}
    {u : Fin r → Fin m → ℂ} {v : Fin r → Fin n → ℂ} (h : IsSchmidt ψ σ u v) (i i' : Fin m) :
    rho ψ i i' = ∑ k, ((σ k : ℂ) ^ 2) * u k i * (starRingEnd ℂ) (u k i') := by
  show (∑ j, ψ i j * (starRingEnd ℂ) (ψ i' j)) = _
  have expand : ∀ j : Fin n, ψ i j * (starRingEnd ℂ) (ψ i' j)
      = ∑ k, ∑ l, (((σ k : ℂ) * u k i) * (starRingEnd ℂ) ((σ l : ℂ) * u l i'))
          * (v k j * (starRingEnd ℂ) (v l j)) := by
    intro j
    rw [h.decomp i j, h.decomp i' j, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul]
    ring
  rw [Finset.sum_congr rfl fun j _ => expand j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_swap_mul (fun l => (((σ k : ℂ) * u k i) * (starRingEnd ℂ) ((σ l : ℂ) * u l i')))
    (fun l j => v k j * (starRingEnd ℂ) (v l j))]
  simp only [conj_on h.onv]
  simp [map_mul]
  ring

/-- The action of the reduced density matrix on a vector, in terms of a Schmidt
decomposition. -/
