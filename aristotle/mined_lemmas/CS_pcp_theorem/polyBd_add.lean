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

theorem polyBd_add {f g : ℕ → ℕ} (hf : PolyBd f) (hg : PolyBd g) :
    PolyBd (fun n => f n + g n) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨a + b + 1, fun n => ?_⟩
  have h1 : f n ≤ (n + 2) ^ (a + b) :=
    (ha n).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h2 : g n ≤ (n + 2) ^ (a + b) :=
    (hb n).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have he : (n + 2) ^ (a + b + 1) = (n + 2) ^ (a + b) * (n + 2) := by ring
  have h3 : (n + 2) ^ (a + b) * 2 ≤ (n + 2) ^ (a + b) * (n + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  show f n + g n ≤ (n + 2) ^ (a + b + 1)
  omega

