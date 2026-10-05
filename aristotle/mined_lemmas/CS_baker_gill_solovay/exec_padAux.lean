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

theorem exec_padAux (O : Oracle) (m r : ℕ) :
    Exec O (.padAux m r) (fun _ => m + 1)
      (fun σ => Function.update σ r (List.replicate m true ++ σ r)) := by
  intro σ rest
  induction m generalizing σ with
  | zero => simp [step, Function.update_eq_self]
  | succ m ih =>
      have h1 : (step O)^[1] (⟨Stmt.padAux (m + 1) r :: rest, σ⟩ : Config)
          = ⟨Stmt.padAux m r :: rest, Function.update σ r (true :: σ r)⟩ := by
        simp [step]
      rw [show m + 1 + 1 = (m + 1) + 1 from rfl, Function.iterate_add_apply, h1,
        ih (Function.update σ r (true :: σ r))]
      congr 1
      funext y
      by_cases hy : y = r <;>
        simp [Function.update_apply, hy, List.replicate_succ, replicate_append_cons]

