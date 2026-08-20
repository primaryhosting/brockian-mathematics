/-
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

open Finset Matrix SimpleGraph

namespace Frontier.Spectral

/-! ## The root of unity `ζ = exp (2 π i / n)` -/

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma eigenvalue_eq (N : ℕ) (mu : ℝ) (x : Fin (N + 3) → ℝ) (hx : x ≠ 0)
    (hL : (cycleGraph (N + 3)).lapMatrix ℝ *ᵥ x = mu • x) :
    ∃ k : Fin (N + 3), mu = 2 - 2 * Real.cos (2 * Real.pi * (k : ℕ) / ((N + 3 : ℕ) : ℝ)) ∧
      ((∑ j, x j) = 0 → (k : ℕ) ≠ 0) := by
  haveI : NeZero (N + 3) := ⟨by omega⟩
  have hn : (N + 3 : ℕ) ≠ 0 := by omega
  have hyne : (fun j => ((x j : ℂ))) ≠ (0 : Fin (N + 3) → ℂ) := by
    intro h
    apply hx
    funext i
    have h1 := congrFun h i
    simp only [Pi.zero_apply] at h1
    exact_mod_cast h1
  have hpoint : ∀ v : Fin (N + 3),
      2 * ((x v : ℂ)) - ((x (v - 1) : ℂ)) - ((x (v + 1) : ℂ)) = (mu : ℂ) * ((x v : ℂ)) := by
    intro v
    have h1 := congrFun hL v
    rw [lap_mulVec] at h1
    have h2 : 2 * x v - x (v - 1) - x (v + 1) = mu * x v := by
      simpa [Pi.smul_apply, smul_eq_mul] using h1
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) h2
  obtain ⟨k, hk⟩ := exists_dft_ne_zero hn (fun j => ((x j : ℂ))) hyne
  have heq := dft_eigen (fun j => ((x j : ℂ))) (mu : ℂ) ((k : ℕ) : ℤ) hpoint
  have hmu : (2 - zeta (N + 3) ^ ((k : ℕ) : ℤ) - zeta (N + 3) ^ (-((k : ℕ) : ℤ))) = (mu : ℂ) :=
    mul_right_cancel₀ hk heq
  have hcos : (mu : ℂ)
      = ((2 - 2 * Real.cos (2 * Real.pi * (k : ℕ) / ((N + 3 : ℕ) : ℝ)) : ℝ) : ℂ) := by
    rw [← hmu]
    have h3 := zeta_zpow_add_neg (n := N + 3) ((k : ℕ) : ℤ)
    push_cast
    push_cast at h3
    linear_combination -h3
  refine ⟨k, by exact_mod_cast hcos, ?_⟩
  intro hsum h0
  apply hk
  rw [h0]
  simp only [Nat.cast_zero, dft, zero_mul, neg_zero, zpow_zero, mul_one]
  have : ∑ j : Fin (N + 3), ((x j : ℂ)) = ((∑ j : Fin (N + 3), x j : ℝ) : ℂ) := by push_cast; rfl
  rw [this, hsum]
  simp

