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

def eqC (V : PCPVerifier n) (r : Fin V.rlen → Bool) (i : Fin V.qnum)
    (r' : Fin V.rlen → Bool) (i' : Fin V.qnum) : Circuit (n + V.wlen) :=
  Circuit.bigAnd ((List.finRange V.plen).map fun j => Circuit.iff (V.posC r i j) (V.posC r' i' j))

/-- Circuit checking consistency of the answers to two queries. -/
