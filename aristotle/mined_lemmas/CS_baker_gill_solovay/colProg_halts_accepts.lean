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

theorem colProg_halts_accepts (O : Oracle) (i k : ℕ) (x : Str) {T : ℕ}
    (hT : 30 + 2 * i + 2 * k + 10 * (x.length + 2) + (x.length + 2) ^ (k + 1) ≤ T) :
    Halts O (colProg i k) x [] T ∧
      (AcceptsIn O (colProg i k) x [] T ↔ O (ENC i k x) = true) := by
  obtain ⟨c, σ', hrun, hσ', hc⟩ := colProg_run O i k x
  have hhalt : ((step O)^[c] (init (colProg i k) x [])).ctrl = [] := by rw [hrun]
  have hstable : runFor O (colProg i k) x [] T = ⟨[], σ'⟩ := by
    unfold runFor
    rw [iterate_step_stable O _ hhalt (le_trans hc hT)]
    exact hrun
  refine ⟨by unfold Halts; rw [hstable], ?_⟩
  unfold AcceptsIn
  rw [hstable]
  simp [hσ']

/-! ## `P` is contained in `NP` -/

