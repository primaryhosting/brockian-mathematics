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

@[simp] theorem eval_imp {N : ℕ} (c d : Circuit N) (v : Fin N → Bool) :
    (Circuit.imp c d).eval v = true ↔ (c.eval v = true → d.eval v = true) := by
  simp only [Circuit.imp, eval]
  cases hc : c.eval v <;> cases hd : d.eval v <;> simp

