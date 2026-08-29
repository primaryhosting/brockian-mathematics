/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Model

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-! ## A calculus for reasoning about program execution -/

/-- `Exec O S n f` says: started with registers `σ`, the statement `S` terminates
after exactly `n σ` steps, leaving the registers in state `f σ` (and the rest of
the control stack untouched). -/

def PLang (O : Oracle) : Set (Set Str) :=
  {L | ∃ (M : Stmt) (k : ℕ),
      (∀ x : Str, Halts O M x [] ((x.length + 2) ^ k)) ∧
      (∀ x : Str, x ∈ L ↔ AcceptsIn O M x [] ((x.length + 2) ^ k))}

/-- `L ∈ NP^O`: some verifier machine, running in time `(n+2)^k`, accepts `x`
together with some witness of length at most `(n+2)^k` exactly when `x ∈ L`. -/
