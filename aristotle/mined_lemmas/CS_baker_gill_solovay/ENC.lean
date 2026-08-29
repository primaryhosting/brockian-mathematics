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

def ENC (i k : ℕ) (x : Str) : Str :=
  List.replicate i true ++ false :: (List.replicate k true ++ false ::
    (dupStr x.reverse ++ true :: false :: List.replicate (encPad k x.length) true))

/-- The deterministic machine which queries `ENC i k x` and copies the answer. -/
