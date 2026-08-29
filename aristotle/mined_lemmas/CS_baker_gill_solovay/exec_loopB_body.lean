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

theorem exec_loopB_body (O : Oracle) :
    Exec O (.seq (.pop 0) (.ite 1 (.seq (.pop 1) (.push 2 true)) (.seq (.pop 1) (.push 2 false))))
      (fun _ => 6)
      (fun σ r => if r = 0 then (σ 0).tail else if r = 1 then (σ 1).tail
        else if r = 2 then ((σ 1).head?.getD false) :: σ 2 else σ r) := by
  have hbr : ∀ b : Bool, Exec O (.seq (.pop 1) (.push 2 b)) (fun _ => 3)
      (fun σ r => if r = 1 then (σ 1).tail else if r = 2 then b :: σ 2 else σ r) := by
    intro b
    refine Exec.congr (exec_seq (exec_pop O 1) (exec_push O 2 b)) (fun σ => by simp)
      (fun σ => ?_)
    funext y
    by_cases h1 : y = 1 <;> by_cases h2 : y = 2 <;> simp [Function.update_apply, h1, h2]
  have hite : Exec O (.ite 1 (.seq (.pop 1) (.push 2 true)) (.seq (.pop 1) (.push 2 false)))
      (fun _ => 4)
      (fun σ r => if r = 1 then (σ 1).tail
        else if r = 2 then ((σ 1).head?.getD false) :: σ 2 else σ r) := by
    refine Exec.congr (exec_ite (hbr true) (hbr false)) (fun σ => by split <;> rfl) (fun σ => ?_)
    by_cases h : (σ 1).head? = some true
    · simp only [h, if_pos]
      funext y
      by_cases h2 : y = 2 <;> simp [h2, h]
    · simp only [h, if_neg, if_false]
      funext y
      by_cases h2 : y = 2 <;> simp [h2]
      cases hh : (σ 1).head? with
      | none => simp
      | some c => cases c with
        | true => exact absurd hh h
        | false => simp
  refine Exec.congr (exec_seq (exec_pop O 0) hite) (fun σ => by simp) (fun σ => ?_)
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> by_cases h2 : y = 2 <;>
    simp [Function.update_apply, h0, h1, h2]

