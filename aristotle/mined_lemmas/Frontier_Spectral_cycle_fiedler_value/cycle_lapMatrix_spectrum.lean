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

theorem cycle_lapMatrix_spectrum (n : ℕ) (hn : 3 ≤ n) :
    {mu : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ (cycleGraph n).lapMatrix ℝ *ᵥ x = mu • x}
      = Set.range (fun k : Fin n => 2 - 2 * Real.cos (2 * Real.pi * (k : ℕ) / n)) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  haveI : NeZero (N + 3) := ⟨by omega⟩
  ext mu
  constructor
  · rintro ⟨x, hx, hLx⟩
    obtain ⟨k, hmu, -⟩ := eigenvalue_eq N mu x hx hLx
    exact ⟨k, hmu.symm⟩
  · rintro ⟨k, rfl⟩
    refine ⟨cycleVec (N + 3) ((k : ℕ) : ℤ), cycleVec_ne_zero _ _, ?_⟩
    have h := cycle_lapMatrix_eigenvector N ((k : ℕ) : ℤ)
    rw [show (2 * Real.pi * (((k : ℕ) : ℤ) : ℝ) / ((N + 3 : ℕ) : ℝ))
      = 2 * Real.pi * ((k : ℕ) : ℝ) / ((N + 3 : ℕ) : ℝ) by push_cast; ring] at h
    exact h

/-- The second-smallest Laplacian eigenvalue of `C n`, i.e. the least nonzero eigenvalue,
equals `2 - 2 cos (2 π / n)`. -/
