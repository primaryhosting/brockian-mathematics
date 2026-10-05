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

theorem qList_len_bound (O : Oracle) (M : Stmt) (x w : Str) (T : ℕ) (s : Str)
    (h : s ∈ qList O (init M x w) T) : s.length ≤ max x.length w.length + T := by
  obtain ⟨j, hj, hq⟩ := mem_qList O (init M x w) T s h
  unfold qry at hq
  cases hc : ((step O)^[j] (init M x w)).ctrl with
  | nil => rw [hc] at hq; simp at hq
  | cons hd tl =>
      rw [hc] at hq
      cases hd with
      | query a b =>
          simp only at hq
          have : s = ((step O)^[j] (init M x w)).regs a := by
            injection hq.symm
          rw [this]
          have := runFor_len O M x w j a
          unfold runFor at this
          omega
      | skip => simp at hq
      | push a b => simp at hq
      | pop a => simp at hq
      | seq a b => simp at hq
      | ite a b c => simp at hq
      | wh a b => simp at hq
      | padAux a b => simp at hq
      | pad a b c => simp at hq

/-! ## Oracles given by finite sets -/

open Classical in
/-- The oracle deciding membership in a finite set. -/
