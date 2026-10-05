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

theorem stage_fst_succ (n : ℕ) :
    (stage (n + 1)).1 =
      if AcceptsIn (oracleOf (stage n).1) (enumPair n).1 (stInput n) [] (stTime n)
        then (stage n).1
        else insert (freshStr (stLen n)
          (qList (oracleOf (stage n).1) (init (enumPair n).1 (stInput n) []) (stTime n)))
          (stage n).1 := rfl

