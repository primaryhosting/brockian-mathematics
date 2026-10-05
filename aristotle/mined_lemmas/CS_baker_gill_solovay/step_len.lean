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

theorem step_len (O : Oracle) (c : Config) (r : ℕ) :
    ((step O c).regs r).length ≤ (c.regs r).length + 1 := by
  unfold step
  match hc : c.ctrl with
  | [] => simp
  | s :: rest =>
    cases s with
    | skip => simp
    | push r' b =>
        by_cases h : r = r' <;> simp [Function.update, h] <;> omega
    | pop r' =>
        by_cases h : r = r' <;> simp [Function.update, h] <;> omega
    | query s' r' =>
        by_cases h : r = r' <;> simp [Function.update, h] <;> omega
    | seq a b => simp
    | ite r' a b => simp
    | wh r' body => by_cases h : c.regs r' = [] <;> simp [h]
    | padAux m r' =>
        cases m with
        | zero => simp
        | succ m => by_cases h : r = r' <;> simp [Function.update, h] <;> omega
    | pad k s' r' => simp

