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

theorem cdot_proj {m n : ℕ} (ψ : Fin m → Fin n → ℂ) (x y : Fin m → ℂ) :
    cdot (fun j => ∑ i, (starRingEnd ℂ) (x i) * ψ i j)
        (fun j => ∑ i, (starRingEnd ℂ) (y i) * ψ i j)
      = cdot y (rho ψ *ᵥ x) := by
  set E : Fin m → Fin m → Fin n → ℂ := fun i i' j =>
    (x i * (starRingEnd ℂ) (ψ i j)) * ((starRingEnd ℂ) (y i') * ψ i' j) with hE
  have lhs : cdot (fun j => ∑ i, (starRingEnd ℂ) (x i) * ψ i j)
      (fun j => ∑ i, (starRingEnd ℂ) (y i) * ψ i j)
      = ∑ i, ∑ i', ∑ j, E i i' j := by
    have step : cdot (fun j => ∑ i, (starRingEnd ℂ) (x i) * ψ i j)
        (fun j => ∑ i, (starRingEnd ℂ) (y i) * ψ i j)
        = ∑ j, ∑ i, ∑ i', E i i' j := by
      simp only [cdot, map_sum, map_mul, Complex.conj_conj, hE]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_mul_sum _ _ _ _
    rw [step, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have rhs : cdot y (rho ψ *ᵥ x) = ∑ i, ∑ i', ∑ j, E i i' j := by
    have step : cdot y (rho ψ *ᵥ x) = ∑ i', ∑ i, ∑ j, E i i' j := by
      simp only [cdot, Matrix.mulVec, dotProduct, rho, Matrix.of_apply, Finset.mul_sum,
        Finset.sum_mul, hE]
      exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring
    rw [step, Finset.sum_comm]
  rw [lhs, rhs]

/-- A vector of zero norm vanishes. -/
