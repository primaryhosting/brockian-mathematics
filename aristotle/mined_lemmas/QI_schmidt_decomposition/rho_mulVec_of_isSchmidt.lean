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

theorem rho_mulVec_of_isSchmidt {m n r : ℕ} {ψ : Fin m → Fin n → ℂ} {σ : Fin r → ℝ}
    {u : Fin r → Fin m → ℂ} {v : Fin r → Fin n → ℂ} (h : IsSchmidt ψ σ u v)
    (w : Fin m → ℂ) (i : Fin m) :
    (rho ψ *ᵥ w) i = ∑ k, ((σ k : ℂ) ^ 2) * cdot (u k) w * u k i := by
  show (∑ i', rho ψ i i' * w i') = _
  have step : ∀ i' : Fin m, rho ψ i i' * w i'
      = ∑ k, (((σ k : ℂ) ^ 2) * u k i) * ((starRingEnd ℂ) (u k i') * w i') := by
    intro i'
    rw [rho_eq_of_isSchmidt h i i', Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl fun i' _ => step i',
    sum_swap_mul (fun k => ((σ k : ℂ) ^ 2) * u k i)
      (fun k i' => (starRingEnd ℂ) (u k i') * w i')]
  exact Finset.sum_congr rfl fun k _ => by rw [cdot]; ring

/-- An orthonormal family is linearly independent. -/
