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

theorem cycle_least_nonzero_eigenvalue (n : ℕ) (hn : 3 ≤ n) :
    IsLeast ({mu : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ (cycleGraph n).lapMatrix ℝ *ᵥ x = mu • x} \ {0})
      (2 - 2 * Real.cos (2 * Real.pi / n)) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  haveI : NeZero (N + 3) := ⟨by omega⟩
  have hpos : 0 < 2 - 2 * Real.cos (2 * Real.pi / ((N + 3 : ℕ) : ℝ)) := by
    have := cos_two_pi_div_lt_one (n := N + 3) (by omega)
    linarith
  constructor
  · refine ⟨⟨cycleVec (N + 3) 1, cycleVec_ne_zero _ 1, ?_⟩, ?_⟩
    · have h := cycle_lapMatrix_eigenvector N 1
      rw [show (2 * Real.pi * ((1 : ℤ) : ℝ) / ((N + 3 : ℕ) : ℝ))
        = 2 * Real.pi / ((N + 3 : ℕ) : ℝ) by push_cast; ring] at h
      exact h
    · simp only [Set.mem_singleton_iff]
      intro h
      rw [h] at hpos
      exact lt_irrefl 0 hpos
  · rintro mu ⟨⟨x, hx, hLx⟩, hmu0⟩
    simp only [Set.mem_singleton_iff] at hmu0
    obtain ⟨k, hmu, -⟩ := eigenvalue_eq N mu x hx hLx
    have hkne : (k : ℕ) ≠ 0 := by
      intro h0
      apply hmu0
      rw [hmu, h0]
      simp
    have hkle : (k : ℕ) ≤ (N + 3) - 1 := by have := k.isLt; omega
    have hcos := cos_le_cos_two_pi_div (n := N + 3) (k := (k : ℕ)) (by omega) (by omega) hkle
    rw [hmu]
    linarith

end Frontier.Spectral

