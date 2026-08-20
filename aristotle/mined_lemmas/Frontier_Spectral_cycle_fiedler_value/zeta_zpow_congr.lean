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

lemma zeta_zpow_congr {n : ℕ} (hn : n ≠ 0) {a b : ℤ} (h : (n : ℤ) ∣ a - b) :
    zeta n ^ a = zeta n ^ b := by
  have h1 : zeta n ^ (a - b) = 1 := (zeta_zpow_eq_one_iff hn _).mpr h
  rw [zpow_sub₀ (zeta_ne_zero n), div_eq_one_iff_eq (zpow_ne_zero _ (zeta_ne_zero n))] at h1
  exact h1

/-- The character sum `∑_{j<n} ζ^{m j}`. -/
