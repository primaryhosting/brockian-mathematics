import Mathlib
/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

namespace Frontier

noncomputable section

/-! ## The model -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

theorem ringZ_eq (k : ℕ) (K : ℝ) :
    ringZ k K = (2 * Real.cosh K) ^ (k + 1) + (2 * Real.sinh K) ^ (k + 1) := by
  have hprod : ∀ σ : Fin (k + 1) → Bool,
      Real.exp (K * ∑ j : Fin (k + 1), spinVal (σ j) * spinVal (σ (j + 1)))
        = (∏ i : Fin k, tw K (σ i.castSucc) (σ i.succ)) * tw K (σ (Fin.last k)) (σ 0) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
    simp only [tw, ← mul_assoc]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.coeSucc_eq_succ, Fin.last_add_one]
  rw [ringZ, Finset.sum_congr rfl (fun σ _ => hprod σ), sum_chain K k (fun a b => tw K b a)]
  simp [tmat_eq, tw, spinVal, pow_succ, Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  ring

/-! ## Base cases of Onsager's solution -/

