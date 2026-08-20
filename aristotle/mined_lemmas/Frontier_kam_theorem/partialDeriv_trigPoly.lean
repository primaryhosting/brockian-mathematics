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

lemma partialDeriv_trigPoly (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ)
    (j : Fin n) (θ : Fin n → ℝ) :
    partialDeriv (trigPoly K a b) j θ =
      ∑ k ∈ K, 2 * π * (k j : ℝ) *
        (-(a k) * Real.sin (2 * π * dotIR k θ) + b k * Real.cos (2 * π * dotIR k θ)) := by
  have key : HasDerivAt (fun s => trigPoly K a b (Function.update θ j s))
      (∑ k ∈ K, 2 * π * (k j : ℝ) *
        (-(a k) * Real.sin (2 * π * dotIR k θ) + b k * Real.cos (2 * π * dotIR k θ))) (θ j) := by
    have hupd : Function.update θ j (θ j) = θ := Function.update_eq_self j θ
    simp only [trigPoly]
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    have hd : HasDerivAt (fun s => 2 * π * dotIR k (Function.update θ j s))
        (2 * π * (k j : ℝ)) (θ j) := by
      simpa using (hasDerivAt_dotIR_update k θ j (θ j)).const_mul (2 * π)
    have hc : HasDerivAt (fun s => Real.cos (2 * π * dotIR k (Function.update θ j s)))
        (-Real.sin (2 * π * dotIR k θ) * (2 * π * (k j : ℝ))) (θ j) := by
      have := (Real.hasDerivAt_cos (2 * π * dotIR k (Function.update θ j (θ j)))).comp (θ j) hd
      rw [hupd] at this
      exact this
    have hs : HasDerivAt (fun s => Real.sin (2 * π * dotIR k (Function.update θ j s)))
        (Real.cos (2 * π * dotIR k θ) * (2 * π * (k j : ℝ))) (θ j) := by
      have := (Real.hasDerivAt_sin (2 * π * dotIR k (Function.update θ j (θ j)))).comp (θ j) hd
      rw [hupd] at this
      exact this
    have := (hc.const_mul (a k)).add (hs.const_mul (b k))
    convert this using 1
    ring
  rw [partialDeriv, key.deriv]

