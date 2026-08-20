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

lemma sub_one_ne_add_one (N : ℕ) (v : Fin (N + 3)) : v - 1 ≠ v + 1 := by
  intro h
  rw [sub_eq_iff_eq_add, add_assoc] at h
  have h0 : (0 : Fin (N + 3)) = 1 + 1 := by simpa using congrArg (fun z => z - v) h
  have h2 : ((0 : Fin (N + 3)) : ℕ) = ((1 + 1 : Fin (N + 3)) : ℕ) := congrArg _ h0
  simp [Fin.val_add, Nat.mod_eq_of_lt] at h2

/-! ## The Laplacian of the cycle graph -/

/-- The Laplacian of `C n` acts as the discrete second difference. -/
