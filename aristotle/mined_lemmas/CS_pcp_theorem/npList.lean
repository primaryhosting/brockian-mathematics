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

def npList (V : PCPVerifier n) : List (Circuit (n + V.wlen)) :=
  ((Finset.univ : Finset (Fin V.rlen → Bool)).toList.map V.decC) ++
    ((Finset.univ : Finset ((((Fin V.rlen → Bool) × Fin V.qnum)) ×
      (((Fin V.rlen → Bool) × Fin V.qnum)))).toList.map
        fun p => V.consC p.1.1 p.1.2 p.2.1 p.2.2)

/-- The NP verification circuit associated with a PCP verifier. -/
