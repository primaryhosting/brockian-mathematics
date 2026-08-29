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

theorem exec_loopB (O : Oracle) :
    Exec O loopB (fun σ => 7 * (σ 0).length + 1)
      (fun σ r => if r = 0 then [] else if r = 1 then (σ 1).drop (σ 0).length
        else if r = 2 then (padTake (σ 0).length (σ 1)).reverse ++ σ 2 else σ r) := by
  have key : ∀ (x : Str) (σ : ℕ → Str), σ 0 = x → ∀ rest : List Stmt,
      (step O)^[7 * x.length + 1] (⟨loopB :: rest, σ⟩ : Config)
        = ⟨rest, fun r => if r = 0 then [] else if r = 1 then (σ 1).drop x.length
            else if r = 2 then (padTake x.length (σ 1)).reverse ++ σ 2 else σ r⟩ := by
    intro x
    induction x with
    | nil =>
        intro σ h0 rest
        have h1 : (step O)^[1] (⟨loopB :: rest, σ⟩ : Config) = ⟨rest, σ⟩ := by
          simp [loopB, step, h0]
        simpa using h1.trans (by
          congr 1
          funext y
          by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;> by_cases hy2 : y = 2 <;>
            simp [hy0, hy1, hy2, h0, padTake])
    | cons b t ih =>
        intro σ h0 rest
        set σ' : ℕ → Str := fun r => if r = 0 then t else if r = 1 then (σ 1).tail
          else if r = 2 then ((σ 1).head?.getD false) :: σ 2 else σ r with hσ'
        have h7 : (step O)^[7] (⟨loopB :: rest, σ⟩ : Config) = ⟨loopB :: rest, σ'⟩ := by
          have hs : (step O)^[1] (⟨loopB :: rest, σ⟩ : Config)
              = ⟨(.seq (.pop 0)
                    (.ite 1 (.seq (.pop 1) (.push 2 true)) (.seq (.pop 1) (.push 2 false))))
                  :: loopB :: rest, σ⟩ := by
            simp [loopB, step, h0]
          rw [show (7 : ℕ) = 6 + 1 from rfl, Function.iterate_add_apply, hs,
            exec_loopB_body O σ (loopB :: rest)]
          congr 1
          funext y
          by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;> by_cases hy2 : y = 2 <;>
            simp [hσ', hy0, hy1, hy2, h0]
        rw [show 7 * (b :: t).length + 1 = (7 * t.length + 1) + 7 from by
          simp [List.length_cons]; ring, Function.iterate_add_apply, h7,
          ih σ' (by simp [hσ']) rest]
        congr 1
        funext y
        by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;> by_cases hy2 : y = 2 <;>
          simp [hσ', hy0, hy1, hy2, padTake, List.drop_tail]
  intro σ rest
  exact key (σ 0) σ rfl rest

/-- Empty register `1`. -/
