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

lemma fin_shift_dvd {n : ℕ} [NeZero n] (u : Fin n) :
    (n : ℤ) ∣ (((u + 1 : Fin n) : ℕ) : ℤ) - (((u : ℕ) : ℤ) + 1) := by
  have hval : ((u + 1 : Fin n) : ℕ) = ((u : ℕ) + 1) % n := by
    rw [Fin.val_add]
    conv_lhs => rw [Fin.val_one']
    rw [Nat.add_mod ((u : ℕ)) (1 % n) n, Nat.mod_mod_of_dvd, ← Nat.add_mod]
    exact dvd_rfl
  rw [hval]
  have h := nat_mod_sub_dvd n ((u : ℕ) + 1)
  push_cast at h ⊢
  exact h

