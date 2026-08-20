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

theorem sum_sq_of_isSchmidt {m n r : ℕ} {ψ : Fin m → Fin n → ℂ} {σ : Fin r → ℝ}
    {u : Fin r → Fin m → ℂ} {v : Fin r → Fin n → ℂ} (h : IsSchmidt ψ σ u v) :
    ∑ k, σ k ^ 2 = ∑ i, ∑ j, ‖ψ i j‖ ^ 2 := by
  have hmc : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq z
  have h1 : ∑ i, rho ψ i i = ((∑ k, σ k ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl fun i _ => rho_eq_of_isSchmidt h i i, Finset.sum_comm]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : ∑ i, ((σ k : ℂ) ^ 2 * u k i * (starRingEnd ℂ) (u k i))
        = (σ k : ℂ) ^ 2 * ∑ i, (u k i * (starRingEnd ℂ) (u k i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, conj_on h.onu k k]
    simp
  have h2 : ∑ i, rho ψ i i = ((∑ i, ∑ j, ‖ψ i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [rho, Matrix.of_apply]
    push_cast
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hmc (ψ i j)]; push_cast; ring
  exact_mod_cast h1.symm.trans h2

/-- Existence of a Schmidt decomposition. -/
