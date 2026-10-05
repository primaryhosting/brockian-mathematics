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

theorem colProg_run (O : Oracle) (i k : ℕ) (x : Str) :
    ∃ (c : ℕ) (σ' : ℕ → Str), (step O)^[c] (init (colProg i k) x []) = ⟨[], σ'⟩ ∧
      σ' 0 = [O (ENC i k x)] ∧
      c ≤ 30 + 2 * i + 2 * k + 10 * (x.length + 2) + (x.length + 2) ^ (k + 1) := by
  refine ⟨_, _, exec_init (x := x) (w := ([] : Str))
    (exec_seq (exec_pad O (k + 1) 0 2) (exec_seq (exec_pad O 1 0 2)
      (exec_seq (exec_push O 2 false) (exec_seq (exec_push O 2 true)
      (exec_seq (exec_loopA O) (exec_seq (exec_push O 2 false)
      (exec_seq (exec_pushRep O k 2 true) (exec_seq (exec_push O 2 false)
      (exec_seq (exec_pushRep O i 2 true) (exec_query O 2 0)))))))))), ?_, ?_⟩
  · simp [init, Function.update_apply, ENC, encPad, List.replicate_add]
  · simp [init]
    ring_nf
    omega

