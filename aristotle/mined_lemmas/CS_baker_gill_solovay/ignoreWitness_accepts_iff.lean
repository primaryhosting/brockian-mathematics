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

theorem ignoreWitness_accepts_iff (O : Oracle) (M : Stmt) (x w : Str) (T : ℕ) :
    AcceptsIn O (ignoreWitness M) x w (T + (2 * w.length + 2)) ↔ AcceptsIn O M x [] T := by
  unfold AcceptsIn runFor
  rw [show T + (2 * w.length + 2) = T + (2 * w.length + 2) from rfl,
    Function.iterate_add_apply, ignoreWitness_run O M x w]

/-! ## The encoding used by the collapsing oracle -/

/-- Length of the padding block in the encoding. -/
