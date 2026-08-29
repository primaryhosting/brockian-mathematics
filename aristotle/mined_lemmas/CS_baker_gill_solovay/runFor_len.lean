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

theorem runFor_len (O : Oracle) (M : Stmt) (x w : Str) (t : ℕ) (r : ℕ) :
    ((runFor O M x w t).regs r).length ≤ max x.length w.length + t := by
  have := iterate_step_len O (init M x w) r t
  refine le_trans this (by
    have : ((init M x w).regs r).length ≤ max x.length w.length := by
      unfold init
      by_cases h0 : r = 0
      · simp [h0]
      · by_cases h1 : r = 1 <;> simp [h0, h1]
    omega)

/-! ## Locality: the computation only depends on the answers to the queries made -/

/-- The queries made during the first `T` steps starting from `c`. -/
