import Mathlib
/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
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

namespace CS

/-! ## Polynomial bounds -/

/-- `PolyBd f` says that `f : ℕ → ℕ` is bounded by a polynomial. -/

theorem polyBd_const (k : ℕ) : PolyBd (fun _ => k) := by
  refine ⟨k, fun n => ?_⟩
  calc k ≤ 2 ^ k := Nat.le_of_lt (Nat.lt_two_pow_self)
    _ ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) k

