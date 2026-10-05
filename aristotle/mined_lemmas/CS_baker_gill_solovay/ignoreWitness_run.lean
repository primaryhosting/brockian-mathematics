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

theorem ignoreWitness_run (O : Oracle) (M : Stmt) (x w : Str) :
    (step O)^[2 * w.length + 2] (init (ignoreWitness M) x w) = init M x [] := by
  have hs : (step O)^[1] (init (ignoreWitness M) x w) = ⟨[clearOne, M], (init M x w).regs⟩ := by
    simp [init, ignoreWitness, step]
  rw [show 2 * w.length + 2 = (2 * w.length + 1) + 1 from rfl, Function.iterate_add_apply, hs]
  have h := exec_clearOne O (init M x w).regs [M]
  rw [show ((fun σ : ℕ → Str => 2 * (σ 1).length + 1) (init M x w).regs)
      = 2 * w.length + 1 from by simp [init]] at h
  rw [h]
  simp only [init, Config.mk.injEq, true_and]
  funext y
  by_cases hy : y = 1 <;> simp [hy]

