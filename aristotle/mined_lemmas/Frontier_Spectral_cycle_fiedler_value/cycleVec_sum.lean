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

lemma cycleVec_sum {n : ℕ} (hn : n ≠ 0) {k : ℤ} (hk : ¬ (n : ℤ) ∣ k) :
    ∑ j : Fin n, cycleVec n k j = 0 := by
  have h : ∑ j : Fin n, cycleVec n k j = (∑ j : Fin n, zeta n ^ (k * (j : ℕ))).re := by
    rw [Complex.re_sum]
    rfl
  rw [h, zeta_char_sum hn k, if_neg hk]
  simp

