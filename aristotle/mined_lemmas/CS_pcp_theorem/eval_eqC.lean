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

@[simp] theorem eval_eqC (r : Fin V.rlen → Bool) (i : Fin V.qnum)
    (r' : Fin V.rlen → Bool) (i' : Fin V.qnum) :
    (V.eqC r i r' i').eval (Fin.append x y) = true ↔
      ∀ j, (V.query i j).eval (Fin.append x r) = (V.query i' j).eval (Fin.append x r') := by
  simp [eqC]

