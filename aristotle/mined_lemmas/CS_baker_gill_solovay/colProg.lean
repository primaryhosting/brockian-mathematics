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

def colProg (i k : ℕ) : Stmt :=
  .seq (.pad (k + 1) 0 2) (.seq (.pad 1 0 2) (.seq (.push 2 false) (.seq (.push 2 true)
    (.seq loopA (.seq (.push 2 false) (.seq (pushRep k 2 true) (.seq (.push 2 false)
      (.seq (pushRep i 2 true) (.query 2 0)))))))))

