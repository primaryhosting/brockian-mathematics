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

theorem ignoreWitness_not_halted (O : Oracle) (M : Stmt) (x w : Str) {t : ℕ}
    (ht : t < 2 * w.length + 2) : ((step O)^[t] (init (ignoreWitness M) x w)).ctrl ≠ [] := by
  intro h
  have hstab := iterate_step_stable O (init (ignoreWitness M) x w) h (le_of_lt ht)
  rw [ignoreWitness_run O M x w] at hstab
  have : (init M x ([] : Str)).ctrl = [] := by rw [hstab, h]
  simp [init] at this

