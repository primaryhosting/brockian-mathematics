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

lemma nat_mod_sub_dvd (n a : ℕ) : (n : ℤ) ∣ ((a % n : ℕ) : ℤ) - (a : ℤ) := by
  refine ⟨-((a / n : ℕ) : ℤ), ?_⟩
  have h : (a : ℤ) = (n : ℤ) * ((a / n : ℕ) : ℤ) + ((a % n : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod a n).symm
  rw [h]; ring

