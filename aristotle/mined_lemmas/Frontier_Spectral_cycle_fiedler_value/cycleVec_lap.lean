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

lemma cycleVec_lap (N : ℕ) (k : ℤ) (v : Fin (N + 3)) :
    2 * cycleVec (N + 3) k v - cycleVec (N + 3) k (v - 1) - cycleVec (N + 3) k (v + 1)
      = (2 - 2 * Real.cos (2 * Real.pi * k / ((N + 3 : ℕ) : ℝ))) * cycleVec (N + 3) k v := by
  have hn : (N + 3 : ℕ) ≠ 0 := by omega
  have hL : zeta (N + 3) ^ (k * (((v - 1 : Fin (N + 3)) : ℕ) : ℤ))
        + zeta (N + 3) ^ (k * (((v + 1 : Fin (N + 3)) : ℕ) : ℤ))
      = ((2 * Real.cos (2 * Real.pi * k / ((N + 3 : ℕ) : ℝ)) : ℝ) : ℂ)
        * zeta (N + 3) ^ (k * ((v : ℕ) : ℤ)) := by
    have h1 : zeta (N + 3) ^ (k * (((v + 1 : Fin (N + 3)) : ℕ) : ℤ))
        = zeta (N + 3) ^ k * zeta (N + 3) ^ (k * ((v : ℕ) : ℤ)) := by
      rw [← zpow_add₀ (zeta_ne_zero _)]
      refine zeta_zpow_congr hn ?_
      obtain ⟨c, hc⟩ := fin_shift_dvd v
      exact ⟨k * c, by linear_combination k * hc⟩
    have h2 : zeta (N + 3) ^ (k * (((v - 1 : Fin (N + 3)) : ℕ) : ℤ))
        = zeta (N + 3) ^ (-k) * zeta (N + 3) ^ (k * ((v : ℕ) : ℤ)) := by
      rw [← zpow_add₀ (zeta_ne_zero _)]
      refine zeta_zpow_congr hn ?_
      obtain ⟨c, hc⟩ := fin_shift_dvd (v - 1)
      rw [sub_add_cancel] at hc
      exact ⟨-(k * c), by linear_combination (-k) * hc⟩
    have h3 := zeta_zpow_add_neg (n := N + 3) k
    have h4 : ((2 * Real.cos (2 * Real.pi * k / ((N + 3 : ℕ) : ℝ)) : ℝ) : ℂ)
        = zeta (N + 3) ^ k + zeta (N + 3) ^ (-k) := by
      rw [h3]
      push_cast
      ring
    rw [h1, h2, h4]
    ring
  have hre := congrArg Complex.re hL
  rw [Complex.add_re, Complex.re_ofReal_mul] at hre
  simp only [cycleVec]
  linarith

/-! ## Monotonicity of the cosine on the relevant range -/

