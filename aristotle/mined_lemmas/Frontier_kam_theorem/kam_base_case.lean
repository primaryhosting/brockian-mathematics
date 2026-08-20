import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

variable {n : ℕ}

/-- Pairing of an integer covector `k` with a real vector `x`: `⟪k, x⟫ = ∑ i, k i * x i`. -/

theorem kam_base_case {n : ℕ} (ω : Fin n → ℝ) (K : Finset (Fin n → ℤ))
    (a b : (Fin n → ℤ) → ℝ) (θ₀ : Fin n → ℝ) :
    IsHamiltonianSolution (kamHam ω K a b 0) (fun t => θ₀ + t • ω) (fun _ => 0) := by
  intro t
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have hpd : partialDeriv (fun y => kamHam ω K a b 0 (θ₀ + t • ω) y) j 0 = ω j := by
      simp only [kamHam]
      exact partialDeriv_linear ω j 0 (0 * trigPoly K a b (θ₀ + t • ω))
    rw [hpd]
    have hlin : (fun s : ℝ => (θ₀ + s • ω) j) = fun s : ℝ => ω j * s + θ₀ j := by
      funext s; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hlin]
    simpa using ((hasDerivAt_id t).const_mul (ω j)).add_const (θ₀ j)
  · have hpd : partialDeriv (fun x => kamHam ω K a b 0 x 0) j (θ₀ + t • ω) = 0 := by
      simp only [kamHam]
      rw [partialDeriv_const_add (fun x => (0 : ℝ) * trigPoly K a b x) _ j (θ₀ + t • ω),
        partialDeriv_const_mul (trigPoly K a b) 0 j (θ₀ + t • ω), zero_mul]
    rw [hpd, neg_zero]
    simpa using (hasDerivAt_const t (0 : ℝ))

/-- The Diophantine hypothesis of `kam_theorem` is non-vacuous: in dimension one every nonzero
frequency `ω` satisfies it with `γ = |ω 0|` and `τ = 1`. -/
