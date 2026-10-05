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

theorem exec_pad (O : Oracle) (k s r : ℕ) :
    Exec O (.pad k s r) (fun σ => (((σ s).length + 2) ^ k + 1) + 1)
      (fun σ => Function.update σ r (List.replicate (((σ s).length + 2) ^ k) true ++ σ r)) := by
  intro σ rest
  have h1 : (step O)^[1] (⟨Stmt.pad k s r :: rest, σ⟩ : Config)
      = ⟨Stmt.padAux (((σ s).length + 2) ^ k) r :: rest, σ⟩ := by
    simp [step]
  rw [Function.iterate_add_apply, h1, exec_padAux O _ r σ rest]

/-- Push `m` copies of the bit `b` onto register `r`. -/
