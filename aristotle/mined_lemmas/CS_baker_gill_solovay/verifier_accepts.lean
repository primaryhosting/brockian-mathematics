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

theorem verifier_accepts (O : Oracle) (x w : Str) {T : ℕ} (hT : 7 * x.length + 3 ≤ T) :
    AcceptsIn O verifier x w T ↔ O (padTake x.length w).reverse = true := by
  obtain ⟨c, σ', hrun, hσ', hc⟩ := verifier_run O x w
  have hhalt : ((step O)^[c] (init verifier x w)).ctrl = [] := by rw [hrun]
  have hstable : runFor O verifier x w T = ⟨[], σ'⟩ := by
    unfold runFor
    rw [iterate_step_stable O _ hhalt (le_trans hc hT)]
    exact hrun
  unfold AcceptsIn
  rw [hstable]
  simp [hσ']

/-! ## Padding a machine so that it ignores its witness -/

