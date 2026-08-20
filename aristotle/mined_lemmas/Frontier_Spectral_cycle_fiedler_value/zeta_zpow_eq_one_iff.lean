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

lemma zeta_zpow_eq_one_iff {n : ℕ} (hn : n ≠ 0) (m : ℤ) :
    zeta n ^ m = 1 ↔ (n : ℤ) ∣ m := by
  rw [zeta_zpow, Complex.exp_eq_one_iff]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h : (m : ℂ) = n * k := by field_simp at hk; exact hk
    exact_mod_cast h
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; field_simp⟩

